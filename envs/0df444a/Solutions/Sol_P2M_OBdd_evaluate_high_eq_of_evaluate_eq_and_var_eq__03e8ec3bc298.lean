-- Prove2me | solution 1 for P2M_OBdd_evaluate_high_eq_of_evaluate_eq_and_var_eq__03e8ec3bc298
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:02.076158+00:00
-- url     : https://prove2.me/submissions/58fa345d-c719-450a-b27e-798422af5e90

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_evaluate_high_eq_evaluate_set_true

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := by
  grind only [!evaluate_high_eq_evaluate_set_true]
end OBdd
