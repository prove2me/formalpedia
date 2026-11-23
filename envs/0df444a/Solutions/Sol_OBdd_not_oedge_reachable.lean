-- Prove2me | solution 1 for OBdd.not_oedge_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:03:07.762707+00:00
-- url     : https://prove2.me/submissions/a6b6c3fd-2fad-4dfd-979c-6da2013bb35d

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_ordered_of_edge
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {n m} {O U : OBdd n m}: OEdge O U → ¬ Reachable O.1.heap U.1.root O.1.root := by
  rintro ⟨same_heap, e⟩ contra
  apply Relation.reflTransGen_iff_eq_or_transGen.mp at contra
  cases contra with
  | inl h =>
    rw [← h] at e
    have : RelevantEdge O.1 O.1.toRelevantPointer O.1.toRelevantPointer := e
    apply O.2 at this
    simp at this
  | inr h =>
    apply transGen_iff_single_and_reflTransGen.mp at h
    rcases h with ⟨c, h1, h2⟩
    rw [same_heap] at h1
    let V : OBdd n m := ⟨{heap := U.1.heap, root := c}, ordered_of_edge (r := rfl) (h := rfl) c h1⟩
    have : c = V.1.root := rfl
    rw [this] at h1 h2
    apply solution ⟨by rfl, h1⟩
    trans O.1.root
    rw [same_heap] at h2; exact h2
    rw [← same_heap]; exact reachable_of_edge e
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end OBdd
