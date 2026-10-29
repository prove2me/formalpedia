-- Prove2me | solution 1 for SphereSOS.DPS.theorem_12_i
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T02:18:40.433724+00:00
-- url     : https://prove2.me/submissions/5b209991-8a34-49a7-8c47-a5c397078de5

import Definitions.Def_SphereSOS_DPS_Setting

open Matrix SphereSOS.DPS
open scoped BigOperators Kronecker ComplexOrder

namespace SphereSepDualProof

lemma trace_product {dA dB : ℕ} (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    (M * ((Matrix.vecMulVec x (star x)) ⊗ₖ (Matrix.vecMulVec y (star y)))).trace =
      pM M (star x) (star y) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_star, pM]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

end SphereSepDualProof

open SphereSepDualProof

theorem solution (dA dB : ℕ) :
    dualCone (SEPcone dA dB) = {M | M.IsHermitian ∧ ∀ x y, 0 ≤ (pM M x y).re} := by
  classical
  ext M
  simp only [dualCone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hM, hdual⟩
    refine ⟨hM, ?_⟩
    intro x y
    have hrank : ((Matrix.vecMulVec (star x) (star (star x))) ⊗ₖ
        (Matrix.vecMulVec (star y) (star (star y)))) ∈ SEPcone dA dB := by
      refine ⟨1, (fun _ => 1), (fun _ => star x), (fun _ => star y), ?_, ?_⟩
      · intro i; norm_num
      · simp
    have h := hdual _ hrank
    rw [trace_product] at h
    simpa only [star_star] using h
  · rintro ⟨hM, hpoly⟩
    refine ⟨hM, ?_⟩
    intro ρ hρ
    rcases hρ with ⟨N, p, x, y, hp, rfl⟩
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, trace_product, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hp i) (hpoly (star (x i)) (star (y i)))
