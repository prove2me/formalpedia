-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankTwoSubspaces_finFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:24:50.769529+00:00
-- url     : https://prove2.me/submissions/9176690f-fb8b-41ea-862e-5d50134ec13f

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
    Nat.card (FiniteGrassmannian k (Fin 4 → k) 2) =
      (Fintype.card k ^ 2 + 1) *
        (Fintype.card k ^ 2 + Fintype.card k + 1) := by
  let q := Fintype.card k
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 2) =
    (q ^ 2 + 1) * (q ^ 2 + q + 1)
  have h := natCard_finiteGrassmannian_mul k (Fin 4 → k) 2 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 2) *
      ((q ^ 2 - 1) * (q ^ 2 - q)) =
    (q ^ 4 - 1) * (q ^ 4 - q) at h
  have hq : 2 ≤ q := by
    apply Nat.succ_le_iff.mpr
    simpa only [q, Nat.card_eq_fintype_card] using
      (Finite.one_lt_card (α := k))
  have hq1 : 1 ≤ q := by omega
  have hp2one : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hp4one : 1 ≤ q ^ 4 := one_le_pow₀ hq1
  have hqp2 : q ≤ q ^ 2 := by
    calc
      q = q * 1 := by simp
      _ ≤ q * q := Nat.mul_le_mul_left q hq1
      _ = q ^ 2 := by ring
  have hqp4 : q ≤ q ^ 4 := by
    calc
      q = q * 1 := by simp
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_left q (one_le_pow₀ hq1)
      _ = q ^ 4 := by ring
  have hqm : q - 1 + 1 = q := Nat.sub_add_cancel hq1
  have h21 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    nlinarith [Nat.sub_add_cancel hp2one, hqm]
  have h2q : q ^ 2 - q = q * (q - 1) := by
    nlinarith [Nat.sub_add_cancel hqp2, hqm]
  have h41 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    nlinarith [Nat.sub_add_cancel hp4one, Nat.sub_add_cancel hp2one]
  have h4q : q ^ 4 - q = q * (q - 1) * (q ^ 2 + q + 1) := by
    nlinarith [Nat.sub_add_cancel hqp4, hqm]
  have hfactor :
      ((q ^ 2 + 1) * (q ^ 2 + q + 1)) *
          ((q ^ 2 - 1) * (q ^ 2 - q)) =
        (q ^ 4 - 1) * (q ^ 4 - q) := by
    rw [h41, h4q, h21, h2q]
    ring
  have hden : 0 < (q ^ 2 - 1) * (q ^ 2 - q) := by
    exact Nat.mul_pos (Nat.sub_pos_of_lt (by nlinarith))
      (Nat.sub_pos_of_lt (by nlinarith))
  exact Nat.eq_of_mul_eq_mul_right hden (h.trans hfactor.symm)
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
