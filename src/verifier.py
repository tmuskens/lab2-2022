from __future__ import annotations
import itertools

from logic import *
from parser import parse
from util import allvars, stringify
from proofrules import *

def verify_leftforall(pf: Proof) -> bool:
    if not pf.rule.name == '@L' or len(pf.premises) != 1:
        return False
    prems = list(set(pf.conclusion.gamma) ^ set(pf.premises[0].gamma))
    if len(prems) != 2:
        return False
    eq = (prems[0].p, prems[1].p) if prems[0] in pf.conclusion.gamma else (prems[1].p, prems[0].p)
    x = eq[0].x
    rho = matchs([(eq[0].p, eq[1])], {})
    if rho is None or x not in rho:
        return False
    if apply_formula(eq[0].p, {x: rho[x]}) != eq[1]:
        return False

    return True

def verify_step(pf: Proof) -> bool:
    if pf.rule.name not in calculus or len(pf.premises) != len(pf.rule.premises):
        return False
    match pf.rule.name:
        case '@L':
            return verify_leftforall(pf)
        case _:
            rhos = matchs_sequent(pf.rule.conclusion, pf.conclusion, {})
            premises = [p.conclusion if isinstance(p, Proof) else p for p in pf.premises]
            for i in range(len(premises)):
                rhos = itertools.chain.from_iterable(
                    matchs_sequent(pf.rule.premises[i], premises[i], rho) for rho in rhos
                )
            rhos = list(rhos)
            for rho in rhos:
                match pf.rule:
                    case Rule(_, _, '@R'):
                        x = Variable('y')
                        context_vars = set().union(*[allvars(p) for p in pf.conclusion.gamma])
                        if rho[x] in context_vars:
                            continue
                        elif not isinstance(rho[x], Variable):
                            continue
                return True
            return False


def verify(pf: Proof) -> list[Sequent]:
    """
    Verify a proof, returning a list of open (unproven) branches
    if there are any.
    
    Args:
        pf (Proof): Proof to verify
    
    Returns:
        list[Sequent]: List described in the summary. If the empty
            list is returned, then the proof has no open branches.
    """
    if isinstance(pf, Sequent):
        return [pf]
    obs = [premise for premise in pf.premises if isinstance(premise, Sequent)]
    if len(obs) > 0 and not verify_step(pf):
        return [pf.conclusion]
    for premise in [premise for premise in pf.premises if isinstance(premise, Proof)]:
        obs += verify(premise)
    return obs
