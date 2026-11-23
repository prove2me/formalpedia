-- Prove2me | solution 1 for OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:19.201083+00:00
-- url     : https://prove2.me/submissions/3f586347-4942-4479-ae5f-a72fb2a8e5c8

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_toTree_eq_toTree_of_ordered_heap_all_reachable_eq
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.evaluate = U.evaluate := by
  intro h1 h2
  ext I
  simp only [OBdd.evaluate, Function.comp_apply]
  rw [toTree_eq_toTree_of_ordered_heap_all_reachable_eq O U h1 h2]
end OBdd
