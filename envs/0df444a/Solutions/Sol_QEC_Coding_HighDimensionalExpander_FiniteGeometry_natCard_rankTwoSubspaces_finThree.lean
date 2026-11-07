-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankTwoSubspaces_finThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:24:52.926648+00:00
-- url     : https://prove2.me/submissions/04626824-6412-40e5-8c7e-58ff115c2f4b

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_finiteGrassmannian_mul

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 3 → k) 2) =
      Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 3 → k) 2 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 3 → k) 2) *
      ((q ^ 2 - 1) * (q ^ 2 - q)) =
    (q ^ 3 - 1) * (q ^ 3 - q) at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hq1 := hq.le
  have hp2one : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hp3one : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hqp2 : q ≤ q ^ 2 := by nlinarith
  have hqp3 : q ≤ q ^ 3 := by nlinarith
  have h21 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    nlinarith [Nat.sub_add_cancel hp2one, Nat.sub_add_cancel hq1]
  have h2q : q ^ 2 - q = q * (q - 1) := by
    nlinarith [Nat.sub_add_cancel hqp2, Nat.sub_add_cancel hq1]
  have h31 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    nlinarith [Nat.sub_add_cancel hp3one, Nat.sub_add_cancel hq1]
  have h3q : q ^ 3 - q = q * (q - 1) * (q + 1) := by
    nlinarith [Nat.sub_add_cancel hqp3, Nat.sub_add_cancel hq1]
  have hfactor : (q ^ 2 + q + 1) * ((q ^ 2 - 1) * (q ^ 2 - q)) =
      (q ^ 3 - 1) * (q ^ 3 - q) := by
    rw [h21, h2q, h31, h3q]
    ring
  have hden : 0 < (q ^ 2 - 1) * (q ^ 2 - q) :=
    Nat.mul_pos (Nat.sub_pos_of_lt (by nlinarith))
      (Nat.sub_pos_of_lt (by nlinarith))
  exact Nat.eq_of_mul_eq_mul_right hden (h.trans hfactor.symm)
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
