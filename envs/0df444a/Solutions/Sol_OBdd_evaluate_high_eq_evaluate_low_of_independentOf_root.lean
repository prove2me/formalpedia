-- Prove2me | solution 1 for OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:02:40.927961+00:00
-- url     : https://prove2.me/submissions/a94d6d3e-96ca-4a01-9ecd-3815f772cda6

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
    Nary.IndependentOf O.evaluate O.1.heap[j].var → (O.high h).evaluate = (O.low h).evaluate := by
  intro i
  ext I
  trans O.evaluate I
  · rw [i true I]
    rw [evaluate_node'' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
    exact (independentOf_lt_root (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩) true I
  · rw [i false I]
    rw [evaluate_node'' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self]
    symm
    exact (independentOf_lt_root (O := O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var  (O := O); simp; rw [h]; simp)⟩) false I
end OBdd
