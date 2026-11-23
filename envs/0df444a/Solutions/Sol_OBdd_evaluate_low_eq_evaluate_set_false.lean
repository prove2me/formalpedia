-- Prove2me | solution 1 for OBdd.evaluate_low_eq_evaluate_set_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:12.807007+00:00
-- url     : https://prove2.me/submissions/fab58027-41bd-4a68-91a0-95bbdd4bc4c0

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
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.low h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var false := by
  ext I
  simp only [Function.comp_apply]
  rw [evaluate_node'' h (j := j)]
  beta_reduce
  simp only [Fin.getElem_fin, Vector.getElem_set_self]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := var_lt_high_var (h := h)
  simp [var] at this
  rw [h] at this
  simp [toVar] at this
  apply independentOf_lt_root (O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var (O := O); simp; rw [h]; simp)⟩
end OBdd
