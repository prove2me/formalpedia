-- Prove2me | solution 1 for OBdd.toTree_usesVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:05.244056+00:00
-- url     : https://prove2.me/submissions/710df6ed-7cd0-49d0-b274-0e77a1848338

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
import Theorems.Thm_DecisionTree_usesVar_iff
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} : O.1.usesVar i ↔ O.toTree.usesVar i := by
  constructor
  · rw [OBdd.usesVar_iff]
    rw [DecisionTree.usesVar_iff]
    rintro ⟨j, hj, h⟩
    rw [toTree_node hj]
    use O.1.heap[j].var, (O.low hj).toTree, (O.high hj).toTree
    cases h with
    | inl h => simp_all
    | inr h =>
      simp only [Fin.getElem_fin, true_and]
      right
      cases h with
      | inl h =>
        left
        rw [solution (O := (O.low hj))] at h
        assumption
      | inr h =>
        right
        rw [solution (O := (O.high hj))] at h
        assumption
  · intro h
    cases O_root_def : O.1.root with
    | terminal _ =>
      rw [toTree_terminal' O_root_def] at h
      contradiction
    | node j =>
      rw [DecisionTree.usesVar_iff] at h
      rcases h with ⟨i', l, h, h1, h2⟩
      rw [toTree_node O_root_def] at h1
      injection h1 with ha hl hh
      cases h2 with
      | inl h2 =>
        use j
        constructor
        · rw [O_root_def]; left
        · simp_all
      | inr h2 =>
        cases h2 with
        | inl h2 =>
          rw [← hl, ← solution] at h2
          exact usesVar_of_low_usesVar h2
        | inr h2 =>
          rw [← hh, ← solution] at h2
          exact usesVar_of_high_usesVar h2
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end OBdd
