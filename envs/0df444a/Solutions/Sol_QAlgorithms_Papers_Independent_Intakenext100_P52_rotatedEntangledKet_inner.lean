-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.rotatedEntangledKet_inner
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T03:51:58.293206+00:00
-- url     : https://prove2.me/submissions/474a4899-e0dd-4075-9b11-d70efbe85e28

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Intakenext100.P52


theorem solution {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U V : Matrix I I ℂ) :
    inner ℂ (rotatedEntangledKet U) (rotatedEntangledKet V) =
      (Fintype.card I : ℂ)⁻¹ * (U * Vᴴ).trace := by
  have hrot (U : Matrix I I ℂ) (i j : I) : rotatedEntangledKet U (i,j) =
      star (U j i) * ((Real.sqrt (Fintype.card I))⁻¹ : ℂ) := by
    simp [rotatedEntangledKet, act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kronecker_apply, Matrix.one_apply, Matrix.conjTranspose_apply, finiteMaxEntangled]
  have hc : (((Real.sqrt (Fintype.card I) : ℝ) : ℂ)⁻¹) ^ 2 =
      (Fintype.card I : ℂ)⁻¹ := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, hrot,
    RCLike.inner_apply, map_mul, star_star]
  simp only [map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
  change _ = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ((((Real.sqrt (Fintype.card I) : ℝ) : ℂ)⁻¹) ^ 2) *
      (U i j * star (V i j)) := by
        simp only [Complex.star_def, Complex.conj_conj]
        ring
    _ = _ := by rw [hc]
