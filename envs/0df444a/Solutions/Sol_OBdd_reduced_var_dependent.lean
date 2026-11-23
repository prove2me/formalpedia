-- Prove2me | solution 1 for OBdd.reduced_var_dependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:39.12984+00:00
-- url     : https://prove2.me/submissions/d75d5687-b2ae-4a24-8b21-f0409c0d176a

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
import Theorems.Thm_OBdd_not_reduced_of_sim_high_low
import Theorems.Thm_OBdd_Canonicity
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} {p : Fin n} :
    O.Reduced → (∀ i : Fin p, Nary.IndependentOf (O.evaluate) ⟨i.1, by omega⟩) → p.1 ≤ O.1.var.1 := by
  intro hr hp
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [Nat.succ_eq_add_one, Bdd.var, Bdd.Ordered.eq_1, O_root_def, Pointer.toVar_terminal_eq]
    exact Fin.le_last p.castSucc
  | node j =>
    by_contra c
    simp only [not_le] at c
    have := hp ⟨O.1.var, by aesop⟩
    simp only [Nat.succ_eq_add_one] at this
    suffices s : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate by
      absurd hr
      apply not_reduced_of_sim_high_low O_root_def
      apply OBdd.Canonicity (OBdd.high_reduced hr) (OBdd.low_reduced hr) s
    ext I
    trans O.evaluate I
    · simp only [Bdd.Ordered.eq_1, Bdd.var, O_root_def, Pointer.toVar_node_eq, Fin.eta] at this
      have := this true I
      rw [this]
      rw [OBdd.evaluate_node'' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [↓reduceIte]
      suffices s : Nary.IndependentOf (O.high O_root_def).evaluate O.1.heap[j.1].var by rw [← s true I]
      refine independentOf_lt_root (O.high O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_high_var
      simp [O_root_def]
    · symm
      simp only [Bdd.Ordered.eq_1, Bdd.var, O_root_def, Pointer.toVar_node_eq, Fin.eta] at this
      have := this false I
      rw [this]
      rw [OBdd.evaluate_node'' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [Bool.false_eq_true, ↓reduceIte]
      suffices s : Nary.IndependentOf (O.low O_root_def).evaluate O.1.heap[j.1].var by rw [s false I]
      refine independentOf_lt_root (O.low O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_low_var
      simp [O_root_def]
end OBdd
