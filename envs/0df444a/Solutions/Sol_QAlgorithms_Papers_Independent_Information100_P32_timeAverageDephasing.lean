-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.timeAverageDephasing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:19:16.770674+00:00
-- url     : https://prove2.me/submissions/163e96e4-9acd-4124-89ac-296b01291373

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7_ee (a b : ℝ) :
    Complex.exp (Complex.I * (a : ℂ)) * conj (Complex.exp (Complex.I * (b : ℂ))) =
      Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal]; ring

theorem X7_evol_diag {J : Type*} [Fintype J] [DecidableEq J] (z : J → ℝ) (φ : ℝ) :
    evolution (Matrix.diagonal fun i => (z i : ℂ)) φ =
      Matrix.diagonal fun i => Complex.exp (Complex.I * ((-(φ * z i) : ℝ) : ℂ)) := by
  unfold evolution
  have hs : ((-(φ : ℂ) * Complex.I) • Matrix.diagonal fun i => (z i : ℂ)) =
      Matrix.diagonal fun i => (-(φ : ℂ) * Complex.I) * (z i : ℂ) := by
    ext i j; simp [Matrix.diagonal_apply]
  rw [hs, Matrix.exp_diagonal, Pi.exp_def]
  congr 1; funext i; rw [← Complex.exp_eq_exp_ℂ]; congr 1; push_cast; ring

theorem X7_dconj {J : Type*} [Fintype J] [DecidableEq J] (v : J → ℂ) (x : Op J) (i j : J) :
    (Matrix.diagonal v * x * (Matrix.diagonal v).conjTranspose) i j = v i * x i j * conj (v j) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]; rfl


theorem X7_exp_bound (d t : ℝ) (hd : d ≠ 0) :
    ‖(Complex.exp ((Complex.I * d) * t) - Complex.exp ((Complex.I * d) * (-t : ℝ))) / (Complex.I * d)‖
      ≤ 2 / |d| := by
  rw [norm_div]
  have h1 : ‖Complex.exp ((Complex.I * d) * t)‖ = 1 := by
    rw [show (Complex.I * d) * t = ((d * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖Complex.exp ((Complex.I * d) * (-t : ℝ))‖ = 1 := by
    rw [show (Complex.I * d) * (-t : ℝ) = ((-(d * t)) : ℝ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have h3 : ‖Complex.I * (d : ℂ)‖ = |d| := by simp
  rw [h3]
  apply div_le_div_of_nonneg_right _ (abs_nonneg d)
  calc _ ≤ ‖Complex.exp ((Complex.I * d) * t)‖ + ‖Complex.exp ((Complex.I * d) * (-t : ℝ))‖ :=
        norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

section

open scoped Matrix.Norms.Elementwise

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (z : I → ℝ) (hz : Function.Injective z) (r : Op I) (hr : IsDensityMatrix r) :
    Tendsto (fun t : ℝ => (2 * t)⁻¹ •
      ∫ s in (-t)..t, evolution (Matrix.diagonal fun i => (z i : ℂ)) s * r * (evolution (Matrix.diagonal fun i => (z i : ℂ)) s).conjTranspose)
      atTop (𝓝 (diagonal r)) := by
  set G : ℝ → Op I := fun s => Matrix.of fun i j =>
    r i j * Complex.exp ((Complex.I * ((z j - z i : ℝ) : ℂ)) * (s : ℂ)) with hGdef
  have hF : ∀ s : ℝ, evolution (Matrix.diagonal fun i => (z i : ℂ)) s * r *
      (evolution (Matrix.diagonal fun i => (z i : ℂ)) s).conjTranspose = G s := by
    intro s; ext i j
    rw [X7_evol_diag, X7_dconj]
    simp only [hGdef, Matrix.of_apply]
    rw [mul_comm _ (r i j), mul_assoc, X7_ee]
    congr 2; push_cast; ring
  simp_rw [hF]
  have hGc : Continuous G := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  have hent : ∀ t : ℝ, ∀ i j, (∫ s in (-t)..t, G s) i j = ∫ s in (-t)..t, G s i j := by
    intro t i j
    let L : Op I →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
    have := L.intervalIntegral_comp_comm (hGc.intervalIntegrable (μ := volume) (-t) t)
    exact this.symm
  refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => ?_))
  simp only [Matrix.smul_apply, hent, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have hc : ∀ t : ℝ, (∫ s in (-t)..t, G s i i) = ((t - -t : ℝ) : ℂ) * r i i := by
      intro t
      simp only [hGdef, Matrix.of_apply, sub_self, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero, mul_one]
      rw [intervalIntegral.integral_const]; simp
    simp only [hc, diagonal, if_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Complex.real_smul]
    push_cast; field_simp; ring
  · have hd : z j - z i ≠ 0 := by
      intro h; exact hij (hz (by linarith)).symm
    have hc : ∀ t : ℝ, (∫ s in (-t)..t, G s i j) = r i j *
        ((Complex.exp ((Complex.I * ((z j - z i : ℝ) : ℂ)) * t) -
          Complex.exp ((Complex.I * ((z j - z i : ℝ) : ℂ)) * (-t : ℝ))) /
          (Complex.I * ((z j - z i : ℝ) : ℂ))) := by
      intro t
      simp only [hGdef, Matrix.of_apply]
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex]
      have : ((z j - z i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
      exact mul_ne_zero Complex.I_ne_zero this
    simp only [hc, diagonal, hij, if_false]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun t : ℝ => (2 * t)⁻¹ * (‖r i j‖ * (2 / |z j - z i|))) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => (2 * t)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
      simpa using this.mul_const (‖r i j‖ * (2 / |z j - z i|))
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (X7_exp_bound _ t hd) (norm_nonneg _)
end
