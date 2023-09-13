from time import time as currenttime
from os import listdir
from os.path import isfile, join
from ortools.sat.python import cp_model
import re
import itertools

class Evaluation:
    def __init__(self):
        self.number_of_instances = 0
        self.total_runtime = 0

class Instance:
    def __init__(self):
        self.number_of_steps = 0
        self.number_of_users = 0
        self.number_of_constraints = 0
        self.authorisations = []
        self.binding_of_duty = []
        self.separation_of_duty = []
        self.at_most_k = []
        self.one_team = []

class SolutionCallback(cp_model.CpSolverSolutionCallback):
    def __init__(self, variables):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0
        self.__solutions = []

    def on_solution_callback(self):
        solution = [self.Value(v) for v in self.__variables]

        if solution not in self.__solutions:
            self.__solutions.append(solution)
            self.__solution_count += 1

        if self.__solution_count > 1:
            self.StopSearch()

    def solution_count(self):
        return self.__solution_count

def read_file(filename):
    def read_attribute(name):
        line = f.readline()
        match = re.match(f"{name}:\\s*(\\d+)$", line)
        
        if match:
            return int(match.group(1))
        else:
            raise Exception("Could not parse line {line}; expected the {name} attribute")

    instance = Instance()

    with open(filename) as f:
        instance.number_of_steps = read_attribute("#Steps")
        instance.number_of_users = read_attribute("#Users")
        instance.number_of_constraints = read_attribute("#Constraints")
        instance.authorisations = [None]*instance.number_of_users
        lines = f.read().lower().splitlines()

        for line in lines:
            if "authorisations" in line:
                user = re.findall("u\d+", line)[0][1:]
                steps = []

                for step in re.findall("s\d+", line):
                    steps.append(int(step[1:]))

                instance.authorisations[int(user) - 1] = steps
            elif "separation-of-duty" in line:
                separations = []

                for seperation in re.findall("s\d+", line):
                    separations.append(int(seperation[1:]))
                
                instance.separation_of_duty.append(separations)
            elif "binding-of-duty" in line:
                bindings = []

                for binding in re.findall("s\d+", line):
                    bindings.append(int(binding[1:]))

                instance.binding_of_duty.append(bindings)
            elif "at-most-k" in line:
                values = line.split()
                k = int(values[1])
                steps = [int(v[1:]) for v in values[2:]]
                instance.at_most_k.append([k, steps])
            elif "one-team" in line:
                steps = re.findall("s\d+", line)
                teams = re.findall(r"\((.*?)\)", line)

                for step in range(len(steps)):
                    steps[step] = int(re.findall("\d+", steps[step])[0])

                for team in range(len(teams)):
                    teams[team] = re.findall("\d+", teams[team])

                instance.one_team.append([teams, steps])

    return instance

def transform_output(d):
    crlf = "\r\n"
    s = []
    s = "".join(kk + crlf for kk in d["sol"])
    s = d["sat"] + crlf + s + d["mul_sol"]
    s = crlf + s + crlf + str(d["exe_time"]) if "exe_time" in d else s
    
    return s

def Solver(filename, **kwargs):
    '''
    :param filename:
    The constraint path

    :param kwargs:

    You may supply extra arguments using the kwargs
    :return:

    A dict.
    '''
    print("\n" + filename)
    instance = read_file(filename)
    print(f"Steps: {instance.number_of_steps}\nUsers: {instance.number_of_users}\nConstraints: {instance.number_of_constraints}")
    model = cp_model.CpModel()
    starttime = int(currenttime() * 1000)
    assignments = []
    bool_vars = {} # dictionary to deal with duplicate boolvars being created
    
    for i in range(instance.number_of_steps):
        assignments.append(model.NewIntVar(1, instance.number_of_users, "s%i" % i))

    # Authorisations
    for user in range(instance.number_of_users):
        for step in range(1, instance.number_of_steps + 1):
            if not instance.authorisations[user] is None:
                if not step in instance.authorisations[user]:
                    model.Add(assignments[step - 1] != user + 1)

    # Separation of duty
    for separations in instance.separation_of_duty:
        model.Add(assignments[separations[0] - 1] != assignments[separations[1] - 1])

    # Binding of duty
    for bindings in instance.binding_of_duty:
        model.Add(assignments[bindings[0] - 1] == assignments[bindings[1] - 1])

    # At most k
    for atmostk in instance.at_most_k:
        k = atmostk[0]
        steps = atmostk[1]

        # group the steps into groups of k+1
        for combination in itertools.combinations(steps, k + 1):
            same_users = [] # array to store boolean variables

            # create intermediate boolean variables to indicate equality of a pair of steps
            for (step1, step2) in itertools.combinations(combination, 2):
                if f"s{step1}=s{step2}" not in bool_vars and f"s{step2}=s{step1}" not in bool_vars:
                    id = model.GetOrMakeIndex(model.NewBoolVar(f"s{step1}=s{step2}"))
                    bool_vars[f"s{step1}=s{step2}"] = id
                else:
                    if f"s{step1}=s{step2}" in bool_vars:
                        id = bool_vars[f"s{step1}=s{step2}"]
                    else:
                        id = bool_vars[f"s{step2}=s{step1}"]
                    
                same = model.GetBoolVarFromProtoIndex(id)
                model.Add(assignments[step1 - 1] == assignments[step2 - 1]).OnlyEnforceIf(same)
                same_users.append(same)

            # there must be at least 1 pair of steps in the group that are equal
            model.AddBoolOr(same_users)

    # One team
    for i in range(len(instance.one_team)):
        teams = instance.one_team[i][0]
        steps = instance.one_team[i][1]
        constraint_steps = []

        for step in steps:
            constraint_steps.append(assignments[step - 1])

        allowed_combinations = []

        for team in teams:
            team_combinations = []

            # generate a Cartesian product of all the user combinations in the team, 
            # making sure that the number of users equal the number of steps by repeating users for some steps
            for product_combinations in itertools.product(team, repeat=len(steps)):
                user_combinations = []
                                
                for user in product_combinations:
                    user_combinations.append(int(user))

                team_combinations.append(user_combinations)

            allowed_combinations += team_combinations

        model.AddAllowedAssignments(constraint_steps, allowed_combinations)

    solver = cp_model.CpSolver()
    solution_callback = SolutionCallback(assignments)
    solver.parameters.enumerate_all_solutions = True
    status = solver.Solve(model, solution_callback)
    endtime = int(currenttime() * 1000)
    d = dict(sat = "unsat", sol = "", mul_sol = "", exe_time = str(endtime - starttime) + "ms")

    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        d["sat"] = "sat"
        dsol = []

        for s, u in enumerate(assignments):
            dsol.append(f"s{s + 1}: u{solver.Value(u)}")

        d["sol"] = dsol
        
        if solution_callback.solution_count() > 1:
            d["mul_sol"] = "other solutions exist"
        else:
            d['mul_sol'] = "this is the only solution"

    return d

if __name__ == "__main__":
    evaluation = Evaluation()
    dpath = "instances"
    files = [join(dpath, f) for f in sorted(listdir(dpath), key=len) if isfile(join(dpath, f)) and "solution" not in f]

    for file in files:
        d = Solver(file, silent=False)
        evaluation.number_of_instances += 1
        evaluation.total_runtime += int(re.match("\d+", d["exe_time"]).group(0))
        print(transform_output(d))

    print(f"Number of instances: {evaluation.number_of_instances}")
    print(f"Total run time: {evaluation.total_runtime}ms")
    print(f"Average run time: {int(evaluation.total_runtime/evaluation.number_of_instances)}ms")