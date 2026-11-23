-- Prove2me | solution 1 for RawBdd.push_evaluate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:56.869929+00:00
-- url     : https://prove2.me/submissions/096ebf42-df61-4d84-b247-87b1ecbe2b01

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
import Theorems.Thm_RawBdd_RawPointer_cook_equiv
import Theorems.Thm_RawBdd_RawNode_cook_equiv
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
open RawBdd
namespace RawBdd
theorem _root_.solution {p : RawPointer} {m : Nat} {hq : p.Bounded m} {n : Nat} {N : RawNode n} {hp : p.Bounded (m + 1)} {v : Vector (RawNode n) m} {h0} {h1} {ho : Bdd.Ordered _} {hu : Bdd.Ordered ⟨cook_heap v h1, RawPointer.cook p hq⟩} :
    OBdd.evaluate ⟨⟨cook_heap (v.push N) h0, RawPointer.cook p hp⟩, ho⟩ =
    OBdd.evaluate ⟨⟨cook_heap v h1, RawPointer.cook p hq⟩, hu⟩ := by
  apply OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
  · simp only [Fin.getElem_fin]
    intro j hj
    use (by omega)
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Fin.is_lt, Vector.getElem_push_lt]
    exact RawNode.cook_equiv
  · exact RawPointer.cook_equiv (h2 := hp)
end RawBdd
