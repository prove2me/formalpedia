-- Prove2me | solution 2 for QiFixedDesign.Concentration.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T19:08:57.550191+00:00
-- url     : https://prove2.me/submissions/fea7cf47-9e3d-4833-be5f-f12a2398cf9d

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_Hat

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

open QiFixedDesign.Concentration

theorem solution {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ)
    (hX : (X.transpose * X).det ≠ 0) :
    (∀ i : Fin N, 0 ≤ hat X i i ∧ hat X i i ≤ 1) ∧
    Matrix.trace (hat X) = ∑ i : Fin N, hat X i i ∧
    (∑ i : Fin N, hat X i i) = (p : ℝ) := by
  have hunit : IsUnit (X.transpose * X).det := isUnit_iff_ne_zero.mpr hX
  have hsym : (hat X).transpose = hat X := by
    simp [hat, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc]
  have hidem : hat X * hat X = hat X := by
    calc
      hat X * hat X = X * (((X.transpose * X)⁻¹ * (X.transpose * X)) *
        (X.transpose * X)⁻¹) * X.transpose := by simp only [hat, Matrix.mul_assoc]
      _ = hat X := by simp [Matrix.nonsing_inv_mul _ hunit, hat]
  have hentry (i j : Fin N) : hat X j i = hat X i j :=
    congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) hsym
  have hsum (i : Fin N) : (∑ j, (hat X i j) ^ 2) = hat X i i := by
    simpa only [Matrix.mul_apply, hentry i, pow_two] using
      congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i i) hidem
  refine ⟨fun i => ?_, rfl, ?_⟩
  · have hsqle : (hat X i i) ^ 2 ≤ hat X i i :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (hat X i j)) (Finset.mem_univ i)).trans_eq
        (hsum i)
    constructor <;> nlinarith [sq_nonneg (hat X i i - 1)]
  · change Matrix.trace (hat X) = (p : ℝ)
    rw [hat, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hunit]
    simp
