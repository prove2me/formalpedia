-- Prove2me | solution 1 for P2M_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq__6f138cebfdfe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:04.832098+00:00
-- url     : https://prove2.me/submissions/e1d44aa8-687f-4693-8aa2-38027a60cf19

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_evaluate_low_eq_evaluate_set_false

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := by
  grind only [evaluate_low_eq_evaluate_set_false, ← evaluate_low_eq_evaluate_set_false]
end OBdd
