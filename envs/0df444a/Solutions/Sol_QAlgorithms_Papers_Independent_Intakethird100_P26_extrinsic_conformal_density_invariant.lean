-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P26.extrinsic_conformal_density_invariant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T01:48:18.424616+00:00
-- url     : https://prove2.me/submissions/2c638250-9950-4853-b02b-c593c6f9ed9a

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P26

noncomputable section

open Set

namespace Aux_P26_ecdi

theorem quad (M : Matrix (Fin 2) (Fin 2) ℝ) (c a : ℝ) :
    (Matrix.trace (c • (M + a • 1))) ^ 2 -
      2 * Matrix.trace ((c • (M + a • 1)) * (c • (M + a • 1))) =
      c ^ 2 * ((Matrix.trace M) ^ 2 - 2 * Matrix.trace (M * M)) := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  ring

end Aux_P26_ecdi

open QAlgorithms.Papers.Independent.Intakethird100.P26 in
theorem solution
    (sigma : Matrix (Fin 2) (Fin 2) ℝ) (hsigma : sigma.PosDef)
    (k : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hk : ∀ i, (k i).IsSymm) (omega : ℝ) (v : Fin 2 → ℝ) :
    extrinsicDensity (weylSurfaceMetric omega sigma)
      (weylSecondForms omega v sigma k) = extrinsicDensity sigma k := by
  have hdet : IsUnit sigma.det := isUnit_iff_ne_zero.mpr hsigma.det_pos.ne'
  obtain ⟨e, he⟩ : ∃ e, e = Real.exp (-2 * omega) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = Real.exp (-omega) := ⟨_, rfl⟩
  have he0 : 0 < e := he ▸ Real.exp_pos _
  have hfe : f ^ 2 = e := by
    rw [hf, he, sq, ← Real.exp_add]; ring_nf
  have hinv : (e • sigma)⁻¹ = e⁻¹ • sigma⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ he0.ne', one_smul,
      Matrix.nonsing_inv_mul _ hdet]
  have hprod : ∀ i, (e • sigma)⁻¹ * (f • (k i + v i • sigma)) =
      (e⁻¹ * f) • (sigma⁻¹ * k i + v i • 1) := by
    intro i
    rw [hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ hdet]
  unfold extrinsicDensity extrinsicQuadratic weylSurfaceMetric weylSecondForms
  rw [← he, ← hf]
  simp only [hprod, Aux_P26_ecdi.quad]
  rw [Matrix.det_smul, Fintype.card_fin, Real.sqrt_mul (by positivity), Real.sqrt_sq he0.le,
    ← Finset.mul_sum]
  have : e * (e⁻¹ * f) ^ 2 = 1 := by
    rw [mul_pow, hfe]; field_simp
  calc e * Real.sqrt sigma.det * ((e⁻¹ * f) ^ 2 * ∑ i : Fin 2,
        ((Matrix.trace (sigma⁻¹ * k i)) ^ 2 - 2 * Matrix.trace (sigma⁻¹ * k i * (sigma⁻¹ * k i))))
      = (e * (e⁻¹ * f) ^ 2) * (Real.sqrt sigma.det * ∑ i : Fin 2,
        ((Matrix.trace (sigma⁻¹ * k i)) ^ 2 - 2 * Matrix.trace (sigma⁻¹ * k i * (sigma⁻¹ * k i)))) := by ring
    _ = _ := by rw [this, one_mul]
