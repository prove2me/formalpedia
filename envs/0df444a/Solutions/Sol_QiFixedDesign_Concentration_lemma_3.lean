-- Prove2me | solution 1 for QiFixedDesign.Concentration.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:48:33.339931+00:00
-- url     : https://prove2.me/submissions/7339c870-1df3-4a5e-9886-e70858baa0c6

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_Hat

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

open QiFixedDesign.Concentration in
theorem solution {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ)
    (hX : (X.transpose * X).det ≠ 0) :
    (∀ i : Fin N, 0 ≤ hat X i i ∧ hat X i i ≤ 1) ∧
    Matrix.trace (hat X) = ∑ i : Fin N, hat X i i ∧
    (∑ i : Fin N, hat X i i) = (p : ℝ) := by
  have hG : IsUnit (X.transpose * X).det := isUnit_iff_ne_zero.mpr hX
  have hinv : (X.transpose * X)⁻¹ * (X.transpose * X) = 1 := Matrix.nonsing_inv_mul _ hG
  have hinv' : (X.transpose * X) * (X.transpose * X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hsym : (hat X).transpose = hat X := by
    simp [hat, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc]
  have hidem : hat X * hat X = hat X := by
    unfold hat
    calc X * (X.transpose * X)⁻¹ * X.transpose * (X * (X.transpose * X)⁻¹ * X.transpose)
        = X * ((X.transpose * X)⁻¹ * (X.transpose * X)) * (X.transpose * X)⁻¹ * X.transpose := by
          simp only [Matrix.mul_assoc]
      _ = X * (X.transpose * X)⁻¹ * X.transpose := by rw [hinv, Matrix.mul_one]
  have hdiag : ∀ i, hat X i i = ∑ j, hat X i j ^ 2 := by
    intro i
    have h := congrFun (congrFun hidem i) i
    rw [Matrix.mul_apply] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    have hs : hat X j i = hat X i j := by
      have := congrFun (congrFun hsym i) j
      rw [Matrix.transpose_apply] at this
      exact this
    rw [hs, pow_two]
  refine ⟨fun i => ?_, rfl, ?_⟩
  · have h1 : hat X i i ^ 2 ≤ ∑ j, hat X i j ^ 2 :=
      Finset.single_le_sum (f := fun j => hat X i j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    rw [← hdiag i] at h1
    have h0 : 0 ≤ hat X i i := le_trans (sq_nonneg _) h1
    exact ⟨h0, by nlinarith⟩
  · change Matrix.trace (hat X) = p
    unfold hat
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv', Matrix.trace_one, Fintype.card_fin]
