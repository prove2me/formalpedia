-- Prove2me | solution 1 for OBdd.usesVar_of_dependsOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:30.786955+00:00
-- url     : https://prove2.me/submissions/c029b5e9-ba36-415d-b03b-54a565d27202

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_OBdd_independentOf_lt_root
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} {i : Fin n} :
    O.evaluate v ≠ O.evaluate (v.set i b) → O.1.usesVar i := by
  intro h
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp [evaluate_terminal' O_root_def] at h
  | node j =>
    cases decEq O.1.heap[j].var i with
    | isFalse hf =>
      cases lt_or_gt_of_ne hf with
      | inl hl =>
        rw [evaluate_node'' O_root_def] at h
        simp only at h
        split at h
        next hh =>
          simp only [Fin.getElem_fin] at h
          simp only [Fin.getElem_fin] at hh
          simp only [Fin.getElem_fin] at hf
          simp_rw [Vector.getElem_set_ne (xs := v) (i := i.1) (j := O.1.heap[j.1].var) (by omega) (by omega) (by omega)] at h
          rw [hh] at h
          simp only [↓reduceIte] at h
          exact usesVar_of_high_usesVar (solution h)
        next hh =>
          simp only [Bool.not_eq_true] at hh
          simp only [Fin.getElem_fin] at h
          simp only [Fin.getElem_fin] at hh
          simp only [Fin.getElem_fin] at hf
          simp_rw [Vector.getElem_set_ne (xs := v) (i := i.1) (j := O.1.heap[j.1].var) (by omega) (by omega) (by omega)] at h
          rw [hh] at h
          simp only [Bool.false_eq_true, ↓reduceIte, ne_eq] at h
          exact usesVar_of_low_usesVar (solution h)
      | inr hr =>
        have := (independentOf_lt_root O ⟨i.1, by simp [var, Bdd.var, O_root_def]; omega⟩) b v
        contradiction
    | isTrue ht =>
      use j
      constructor
      · rw [O_root_def]; left
      · exact ht
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end OBdd
