-- Prove2me | solution 1 for OBdd.dependsOn_of_usesVar_of_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:56.434294+00:00
-- url     : https://prove2.me/submissions/5b92359a-376e-4800-a570-dc31967320d4

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_OBdd_independentOf_lt_root
import Theorems.Thm_OBdd_high_reduced
import Theorems.Thm_OBdd_low_reduced
import Theorems.Thm_OBdd_evaluate_high_eq_evaluate_set_true
import Theorems.Thm_OBdd_evaluate_low_eq_evaluate_set_false
import Theorems.Thm_OBdd_not_reduced_of_sim_high_low
import Theorems.Thm_OBdd_Canonicity
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} :
    O.Reduced → Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var = i → ∃ v : Vector Bool n, O.evaluate v ≠ O.evaluate (v.set i true) := by
  intro hr hj hi
  rcases O_def : O with ⟨⟨heap, root⟩, o⟩
  letI O : OBdd n m := ⟨⟨heap, root⟩, o⟩
  subst hi
  simp_all only
  cases Relation.reflTransGen_swap.mp hj with
  | refl =>
    rw [evaluate_node'' rfl]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte, ne_eq]
    rw [← not_forall]
    intro contra
    apply not_reduced_of_sim_high_low (O := O) rfl
    · apply OBdd.Canonicity
      · exact high_reduced hr
      · exact low_reduced hr
      · ext x
        have h1 : heap[j].var = O.var := by rfl
        have h2 := contra (x.set heap[j].var false)
        simp only [Fin.getElem_fin, Vector.getElem_set_self, Bool.false_eq_true, ↓reduceIte,
          Vector.set_set] at h2
        calc _
          _ = (O.high rfl).evaluate (x.set heap[j].var true) := by
            have hhi : heap[j].var.1 < (O.high rfl).var := by
              rw [h1]
              apply var_lt_high_var
            apply independentOf_lt_root (O.high rfl) ⟨heap[j].var.1, hhi⟩
          _ = (O.low rfl).evaluate (x.set heap[j].var false) := by symm; assumption
          _ = _ := by
            symm
            have hhi : heap[j].var.1 < (O.low rfl).var := by
              rw [h1]
              apply var_lt_low_var
            apply independentOf_lt_root (O.low rfl) ⟨heap[j].var.1, hhi⟩
    · exact hr
  | tail r e =>
    rename_i p
    apply Relation.reflTransGen_swap.mpr at r
    cases root with
    | terminal _ => contradiction
    | node jr =>
      cases e with
      | low  he =>
        have := solution ((low_reduced (h := rfl) hr)) (by simp_all [low, Bdd.low]; exact r) (i := heap[j].var) rfl
        rcases this with ⟨v, hv⟩
        use v.set heap[jr].var false
        contrapose hv
        calc _
          _ = evaluate O (v.set (heap[jr.1].var.1) false) := by
            rw [evaluate_low_eq_evaluate_set_false]
            rfl
          _ = O.evaluate ((v.set (heap[jr.1].var.1) false).set heap[j].var true) := hv
          _ = O.evaluate ((v.set heap[j].var true).set (heap[jr.1].var.1) false) := by
            rw [Vector.set_comm]
            apply ne_of_lt
            have := var_lt_low_var (O := O) (h := rfl)
            simp only [var, Nat.succ_eq_add_one, Bdd.var, Ordered, O, toVar_node_eq,
              low, Bdd.low] at this
            rw [he] at this
            simp only [Fin.getElem_fin] at this
            apply lt_of_lt_of_le this
            rw [show heap[j].var = (toVar heap (node j)).1 by simp [toVar]]
            let B : Bdd n m := ⟨heap, p⟩
            rw [show heap = B.heap by rfl]
            rw [show p = B.root by rfl]
            apply mayPrecede_of_reachable
            · simp only [B]
              rw [← he]
              exact OBdd.ordered_of_low_edge o
            · exact r
          _ = (O.low rfl).evaluate (v.set heap[j].var true) := by
            symm
            rw [evaluate_low_eq_evaluate_set_false]
            rfl
      | high he =>
        have := solution (high_reduced (h := rfl) hr) (by simp_all [high, Bdd.high]; exact r) (i := heap[j].var) rfl
        rcases this with ⟨v, hv⟩
        use v.set heap[jr].var true
        contrapose hv
        calc _
          _ = O.evaluate (v.set (heap[jr.1].var.1) true) := by
            rw [evaluate_high_eq_evaluate_set_true]
            rfl
          _ = O.evaluate ((v.set (heap[jr.1].var.1) true).set heap[j].var true) := hv
          _ = O.evaluate ((v.set heap[j].var true).set (heap[jr.1].var.1) true) := by
            rw [Vector.set_comm]
            apply ne_of_lt
            have := var_lt_high_var (O := O) (h := rfl)
            simp only [var, Nat.succ_eq_add_one, Bdd.var, Ordered, O, toVar_node_eq, high, Bdd.high, he] at this
            simp only [Fin.getElem_fin] at this
            apply lt_of_lt_of_le this
            rw [show heap[j].var = (toVar heap (node j)).1 by simp [toVar]]
            let B : Bdd n m := ⟨heap, p⟩
            rw [show p = B.root by rfl]
            apply mayPrecede_of_reachable
            · simp only [B]
              rw [← he]
              apply OBdd.ordered_of_high_edge
              exact o
            · exact r
          _ = (O.high rfl).evaluate (v.set heap[j].var true) := by
            symm
            rw [evaluate_high_eq_evaluate_set_true]
            rfl
termination_by O
decreasing_by
  · simp [O_def, flip, oedge_of_low]
  · simp [O_def, flip, oedge_of_high]
end OBdd
