-- Prove2me | solution 1 for TaoBR.not_restr_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:46:24.66725+00:00
-- url     : https://prove2.me/submissions/30f4586c-1aef-4935-9508-0a9dc789ed69

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  ContDiff Pointwise

namespace TaoBR.NotRestr

/-- Surface measure pushed forward to `E n`. -/
noncomputable def nr_mu (n : ℕ) : Measure (E n) := (sphereMeasure n).map Subtype.val

instance nr_sphere_finite (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  unfold sphereMeasure; infer_instance

instance nr_mu_finite (n : ℕ) : IsFiniteMeasure (nr_mu n) := by
  unfold nr_mu sphereMeasure; infer_instance

noncomputable def nr_F (n : ℕ) : E n → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar (nr_mu n) (innerSL ℝ).toLinearMap₁₂
    (fun _ => (1 : ℂ))

lemma nr_F_apply (n : ℕ) (x : E n) :
    nr_F n x = ∫ v, 𝐞 (-⟪v, x⟫) • (1 : ℂ) ∂(nr_mu n) := rfl

lemma nr_mu_ae (n : ℕ) : ∀ᵐ v ∂(nr_mu n), ‖v‖ = 1 := by
  unfold nr_mu
  rw [ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_eq_fun measurable_norm measurable_const)]
  exact ae_of_all _ (fun y => by simp)

lemma nr_F_contDiff (n : ℕ) : ContDiff ℝ ∞ (nr_F n) := by
  unfold nr_F
  apply VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ)
  intro k _
  refine (integrable_const (1 : ℝ)).congr ?_
  filter_upwards [nr_mu_ae n] with v hv
  simp [hv]

noncomputable def nr_M (n : ℕ) : ℝ := (nr_mu n).real Set.univ

lemma nr_F_norm_le (n : ℕ) (x : E n) : ‖nr_F n x‖ ≤ nr_M n := by
  rw [nr_F_apply, nr_M]
  have := norm_integral_le_of_norm_le_const (μ := nr_mu n)
    (f := fun v : E n => 𝐞 (-⟪v, x⟫) • (1 : ℂ)) (C := 1)
    (ae_of_all _ (fun v => by rw [Circle.norm_smul]; simp))
  simpa using this

lemma nr_mult (n : ℕ) {f : E n → ℂ} (hf : Integrable f) :
    ∫ ξ, 𝓕 f ξ ∂(nr_mu n) = ∫ x, f x * nr_F n x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := nr_mu n)
    (L := innerₗ (E n)) (e := Real.fourierChar) (g := fun _ => (1 : ℂ))
    Real.continuous_fourierChar continuous_inner hf (integrable_const _)
  simp only [smul_eq_mul, mul_one] at this
  calc ∫ ξ, 𝓕 f ξ ∂(nr_mu n)
      = ∫ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ (E n)) f ξ ∂nr_mu n := rfl
    _ = _ := this
    _ = _ := by
      congr 1; ext x; congr 1
      rw [nr_F_apply]
      simp [VectorFourier.fourierIntegral, real_inner_comm]


/-- The cutoff bump, equal to `1` on `closedBall 0 (N+1)` and supported in `closedBall 0 (N+2)`. -/
noncomputable def nr_chi (n : ℕ) (N : ℕ) : ContDiffBump (0 : E n) :=
  ⟨N + 1, N + 2, by positivity, by linarith⟩

lemma nr_dual_step (n : ℕ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (C : ℝ≥0)
    (hC : ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
      eLpNorm (restriction f) p (sphereMeasure n) ≤
        C * ENNReal.ofReal (R ^ (0 : ℝ)) * eLpNorm f p (volume.restrict (closedBall 0 R)))
    (w : E n → ℝ) (hw : ContDiff ℝ ∞ w) (hw0 : ∀ x, 0 ≤ w x) (N : ℕ) :
    ENNReal.ofReal (∫ x, nr_chi n N x * w x * ‖nr_F n x‖ ^ 2) ≤
      C * (sphereMeasure n Set.univ) ^ (1 - 1 / p.toReal) *
        eLpNorm (fun x => (w x : ℂ) * nr_F n x) p volume := by
  set χ := nr_chi n N
  set f : E n → ℂ := fun x => ((χ x : ℝ) : ℂ) * (w x : ℂ) * conj (nr_F n x) with hf_def
  have hfd : ContDiff ℝ ∞ f :=
    ((Complex.ofRealCLM.contDiff.comp χ.contDiff).mul (Complex.ofRealCLM.contDiff.comp hw)).mul
      (Complex.conjCLE.contDiff.comp (nr_F_contDiff n))
  have hfs : HasCompactSupport f := by
    have h1 : HasCompactSupport (fun x => ((χ x : ℝ) : ℂ)) :=
      χ.hasCompactSupport.comp_left Complex.ofReal_zero
    exact (h1.mul_right (f' := fun x => (w x : ℂ))).mul_right
  have hfi : Integrable f := hfd.continuous.integrable_of_hasCompactSupport hfs
  set φ := hfs.toSchwartzMap hfd
  have hφ : (φ : E n → ℂ) = f := rfl
  have hsupp : tsupport φ ⊆ closedBall 0 ((N : ℝ) + 2) := by
    rw [hφ]
    refine (tsupport_mul_subset_left).trans ((tsupport_mul_subset_left).trans ?_)
    refine (tsupport_comp_subset Complex.ofReal_zero _).trans ?_
    rw [χ.tsupport_eq]
    rfl
  have h1 := hC ((N : ℝ) + 2) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]) φ hsupp
  rw [Real.rpow_zero, ENNReal.ofReal_one, mul_one] at h1
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hfi
  have hint_nonneg : 0 ≤ ∫ x, χ x * w x * ‖nr_F n x‖ ^ 2 :=
    integral_nonneg (fun x => mul_nonneg (mul_nonneg (χ.nonneg) (hw0 x)) (by positivity))
  have hfF : ∀ x, f x * nr_F n x = ((χ x * w x * ‖nr_F n x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    simp only [hf_def, mul_assoc, Complex.conj_mul']
    push_cast; ring
  have e1 : ENNReal.ofReal (∫ x, χ x * w x * ‖nr_F n x‖ ^ 2) = ‖∫ ξ, 𝓕 f ξ ∂(nr_mu n)‖ₑ := by
    rw [nr_mult n hfi, integral_congr_ae (ae_of_all _ hfF), integral_complex_ofReal,
      ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hint_nonneg]
  have e2 : ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ∂(nr_mu n) = eLpNorm (restriction φ) 1 (sphereMeasure n) := by
    rw [eLpNorm_one_eq_lintegral_enorm, nr_mu, lintegral_map hcont.measurable.enorm
      measurable_subtype_coe]
    rfl
  have hmeas : AEStronglyMeasurable (restriction φ) (sphereMeasure n) :=
    (hcont.comp continuous_subtype_val).aestronglyMeasurable
  have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hmeas
  have h4 : eLpNorm φ p (volume.restrict (closedBall 0 ((N : ℝ) + 2))) ≤
      eLpNorm (fun x => (w x : ℂ) * nr_F n x) p volume := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (eLpNorm_mono (fun x => ?_))
    rw [hφ]
    simp only [hf_def, norm_mul, Complex.norm_real, Complex.norm_conj]
    have : ‖χ x‖ ≤ 1 := by rw [Real.norm_of_nonneg χ.nonneg]; exact χ.le_one
    calc ‖χ x‖ * ‖w x‖ * ‖nr_F n x‖ ≤ 1 * ‖w x‖ * ‖nr_F n x‖ := by gcongr
      _ = _ := by ring
  calc ENNReal.ofReal (∫ x, χ x * w x * ‖nr_F n x‖ ^ 2)
      ≤ ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ∂(nr_mu n) := e1 ▸ enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (restriction φ) 1 (sphereMeasure n) := e2
    _ ≤ eLpNorm (restriction φ) p (sphereMeasure n) *
          (sphereMeasure n Set.univ) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := h3
    _ ≤ C * eLpNorm (fun x => (w x : ℂ) * nr_F n x) p volume *
          (sphereMeasure n Set.univ) ^ (1 - 1 / p.toReal) := by
        simp only [ENNReal.toReal_one, div_one]
        gcongr
        exact h1.trans (by gcongr)
    _ = _ := by ring


lemma nr_F_continuous (n : ℕ) : Continuous (nr_F n) :=
  (nr_F_contDiff n).continuous

lemma nr_wF_integrable (n : ℕ) {w : E n → ℝ} (hwi : Integrable w) :
    Integrable (fun x => w x * ‖nr_F n x‖ ^ 2) :=
  hwi.mul_bdd (c := nr_M n ^ 2) ((nr_F_continuous n).norm.pow 2).aestronglyMeasurable
    (ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (nr_F_norm_le n x) 2))

lemma nr_dual (n : ℕ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (h : Restr n p 0) :
    ∃ K₀ : ℝ≥0∞, K₀ ≠ ⊤ ∧ ∀ w : E n → ℝ, ContDiff ℝ ∞ w → Integrable w → (∀ x, 0 ≤ w x) →
      ENNReal.ofReal (∫ x, w x * ‖nr_F n x‖ ^ 2) ≤
        K₀ * eLpNorm (fun x => (w x : ℂ) * nr_F n x) p volume := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * (sphereMeasure n Set.univ) ^ (1 - 1 / p.toReal), ?_, ?_⟩
  · refine ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_nonneg ?_ ?_)
    · rw [sub_nonneg]
      rcases eq_or_ne p ⊤ with rfl | hpt
      · simp
      · have : 1 ≤ p.toReal := by
          have := ENNReal.toReal_mono hpt hp1; simpa using this
        exact div_le_one_of_le₀ this (by linarith)
    · exact measure_ne_top _ _
  intro w hw hwi hw0
  have hlim : Tendsto (fun N : ℕ => ∫ x, nr_chi n N x * w x * ‖nr_F n x‖ ^ 2) atTop
      (𝓝 (∫ x, w x * ‖nr_F n x‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => w x * ‖nr_F n x‖ ^ 2)
      (fun N => ?_) (nr_wF_integrable n hwi) (fun N => ae_of_all _ (fun x => ?_))
      (ae_of_all _ (fun x => ?_))
    · exact ((((nr_chi n N).continuous).mul hw.continuous).mul
        ((nr_F_continuous n).norm.pow 2)).aestronglyMeasurable
    · have h0 := (nr_chi n N).nonneg (x := x)
      have h1 := (nr_chi n N).le_one (x := x)
      rw [Real.norm_of_nonneg (by have := hw0 x; positivity)]
      have : 0 ≤ w x * ‖nr_F n x‖ ^ 2 := by have := hw0 x; positivity
      calc nr_chi n N x * w x * ‖nr_F n x‖ ^ 2 = nr_chi n N x * (w x * ‖nr_F n x‖ ^ 2) := by
            ring
        _ ≤ 1 * (w x * ‖nr_F n x‖ ^ 2) := by gcongr
        _ = _ := one_mul _
    · refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨⌈‖x‖⌉₊, fun N hN => ?_⟩
      have : nr_chi n N x = 1 := by
        apply ContDiffBump.one_of_mem_closedBall
        rw [mem_closedBall, dist_zero_right]
        show ‖x‖ ≤ (N : ℝ) + 1
        have := Nat.le_ceil ‖x‖
        have : (⌈‖x‖⌉₊ : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      rw [this, one_mul]
  exact le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp hlim)
    (fun N => nr_dual_step n hp1 C hC w hw hw0 N)


/-- The Gaussian `exp(-π|x|²/r²)`. -/
noncomputable def nr_G (n : ℕ) (r : ℝ) (x : E n) : ℝ := Real.exp (-(Real.pi / r ^ 2) * ‖x‖ ^ 2)

lemma nr_G_eq_cexp (n : ℕ) (r : ℝ) (x : E n) :
    ((nr_G n r x : ℝ) : ℂ) = Complex.exp (-((Real.pi / r ^ 2 : ℝ) : ℂ) * ‖x‖ ^ 2) := by
  rw [nr_G, Complex.ofReal_exp]; push_cast; ring_nf

lemma nr_G_integrable (n : ℕ) {r : ℝ} (hr : 0 < r) : Integrable (nr_G n r) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E n)
    (b := ((Real.pi / r ^ 2 : ℝ) : ℂ)) (by simp only [Complex.ofReal_re]; positivity) 0 0
  refine h.norm.congr (ae_of_all _ fun x => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_exp]
  rw [nr_G]
  congr 1
  simp [← Complex.ofReal_pow]

lemma nr_G_nonneg (n : ℕ) (r : ℝ) (x : E n) : 0 ≤ nr_G n r x := (Real.exp_pos _).le

lemma nr_e_smul (t : ℝ) : 𝐞 t • (1 : ℂ) = Complex.exp (↑(2 * Real.pi * t) * Complex.I) := by
  rw [Circle.smul_def, smul_eq_mul, mul_one, Real.fourierChar_apply]

lemma nr_conj_F (n : ℕ) (x : E n) :
    conj (nr_F n x) = ∫ η, Complex.exp (↑(2 * Real.pi * ⟪η, x⟫) * Complex.I) ∂(nr_mu n) := by
  rw [nr_F_apply, ← integral_conj]
  congr 1; ext η
  rw [nr_e_smul, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

lemma nr_rpow_half (n : ℕ) {r : ℝ} (hr : 0 < r) : (r ^ 2) ^ ((n : ℝ) / 2) = r ^ n := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast]
  congr 1; push_cast; ring

lemma nr_fourier_gauss (n : ℕ) {r : ℝ} (hr : 0 < r) (η ξ : E n) :
    𝓕 (fun v : E n => Complex.exp (-((Real.pi / r ^ 2 : ℝ) : ℂ) * ‖v‖ ^ 2 +
        2 * Real.pi * Complex.I * ⟪η, v⟫)) ξ =
      ((r ^ n * Real.exp (-(Real.pi * r ^ 2) * ‖η - ξ‖ ^ 2) : ℝ) : ℂ) := by
  rw [fourier_gaussian_innerProductSpace' (by simp only [Complex.ofReal_re]; positivity),
    finrank_euclideanSpace_fin]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr2 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e1 : (Real.pi : ℂ) / ((Real.pi / r ^ 2 : ℝ) : ℂ) = ((r ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [e1, ← Complex.ofReal_natCast n, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_div,
    ← Complex.ofReal_cpow (by positivity), nr_rpow_half n hr, Complex.ofReal_mul,
    Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp


lemma nr_fourier_H (n : ℕ) {r : ℝ} (hr : 0 < r) (ξ : E n) :
    𝓕 (fun x => ((nr_G n r x : ℝ) : ℂ) * conj (nr_F n x)) ξ =
      ∫ η, ((r ^ n * Real.exp (-(Real.pi * r ^ 2) * ‖η - ξ‖ ^ 2) : ℝ) : ℂ) ∂(nr_mu n) := by
  set b : ℂ := ((Real.pi / r ^ 2 : ℝ) : ℂ)
  set k : E n → E n → ℂ := fun x η =>
    𝐞 (-⟪x, ξ⟫) • Complex.exp (-b * ‖x‖ ^ 2 + 2 * Real.pi * Complex.I * ⟪η, x⟫) with hk
  have step1 : ∀ x, 𝐞 (-⟪x, ξ⟫) • (((nr_G n r x : ℝ) : ℂ) * conj (nr_F n x)) =
      ∫ η, k x η ∂(nr_mu n) := by
    intro x
    rw [nr_conj_F, ← integral_const_mul, Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    congr 1; ext η
    simp only [hk, Circle.smul_def, smul_eq_mul]
    congr 1
    rw [nr_G_eq_cexp, ← Complex.exp_add]
    congr 1; simp only [b]; push_cast; ring
  have hint : Integrable (Function.uncurry k) ((volume : Measure (E n)).prod (nr_mu n)) := by
    refine Integrable.mono' ((nr_G_integrable n hr).mul_prod (integrable_const (1 : ℝ))) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hk, Function.uncurry_def]
      exact (Real.continuous_fourierChar.comp (by fun_prop)).smul (by fun_prop)
    · refine ae_of_all _ (fun z => ?_)
      simp only [hk, Function.uncurry_def, Circle.norm_smul, Complex.norm_exp, mul_one, nr_G]
      apply le_of_eq
      congr 1
      simp [b, ← Complex.ofReal_pow]
  rw [Real.fourier_eq]
  simp_rw [step1]
  rw [integral_integral_swap hint]
  congr 1; ext η
  rw [← nr_fourier_gauss n hr η ξ, Real.fourier_eq]

lemma nr_gauss_identity (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x, nr_G n r x * ‖nr_F n x‖ ^ 2 =
      ∫ ξ, ∫ η, r ^ n * Real.exp (-(Real.pi * r ^ 2) * ‖η - ξ‖ ^ 2) ∂(nr_mu n) ∂(nr_mu n) := by
  have hH : Integrable (fun x => ((nr_G n r x : ℝ) : ℂ) * conj (nr_F n x)) :=
    (nr_G_integrable n hr).ofReal.mul_bdd (c := nr_M n)
      (Complex.continuous_conj.comp (nr_F_continuous n)).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Complex.norm_conj]; exact nr_F_norm_le n x))
  have h := nr_mult n hH
  simp_rw [nr_fourier_H n hr, integral_complex_ofReal] at h
  have h2 : ∀ x, ((nr_G n r x : ℝ) : ℂ) * conj (nr_F n x) * nr_F n x =
      ((nr_G n r x * ‖nr_F n x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [mul_assoc, Complex.conj_mul']; push_cast; ring
  simp_rw [h2, integral_complex_ofReal] at h
  exact_mod_cast h.symm


lemma nr_ball_sub_cone (n : ℕ) {η : E n} (hη : ‖η‖ = 1) {t s : ℝ} (ht0 : 0 < t)
    (hs1 : 1 / 2 ≤ s) (hs2 : s ≤ 3 / 4) (ht1 : t ≤ 1) :
    ball (s • η) (t / 8) ⊆ Set.Ioo (0 : ℝ) 1 • (sphere (0 : E n) 1 ∩ closedBall η t) := by
  intro y hy
  rw [mem_ball, dist_eq_norm] at hy
  have hsη : ‖s • η‖ = s := by rw [norm_smul, hη, Real.norm_of_nonneg (by linarith), mul_one]
  have h1 : |‖y‖ - s| ≤ ‖y - s • η‖ := by
    have := abs_norm_sub_norm_le y (s • η); rwa [hsη] at this
  have hy0 : 3 / 8 ≤ ‖y‖ := by have := (abs_le.1 h1).1; linarith
  have hy1 : ‖y‖ < 1 := by have := (abs_le.1 h1).2; linarith
  have hyne : ‖y‖ ≠ 0 := by linarith
  rw [Set.mem_smul]
  refine ⟨‖y‖, ⟨by linarith, hy1⟩, ‖y‖⁻¹ • y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyne]
  · rw [mem_closedBall, dist_eq_norm]
    have e : ‖y‖⁻¹ • y - η = ‖y‖⁻¹ • (y - ‖y‖ • η) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hyne, one_smul]
    have h2 : ‖y - ‖y‖ • η‖ ≤ ‖y - s • η‖ + |‖y‖ - s| := by
      have : y - ‖y‖ • η = (y - s • η) - (‖y‖ - s) • η := by rw [sub_smul]; abel
      rw [this]; refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, hη, mul_one, Real.norm_eq_abs]
    rw [e, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_right hy0 ht0.le
    linarith
  · rw [smul_smul, mul_inv_cancel₀ hyne, one_smul]

lemma nr_mu_closedBall (n : ℕ) (η : E n) (t : ℝ) :
    nr_mu n (closedBall η t) =
      n * volume (Set.Ioo (0 : ℝ) 1 • (sphere (0 : E n) 1 ∩ closedBall η t)) := by
  rw [nr_mu, Measure.map_apply measurable_subtype_coe measurableSet_closedBall, sphereMeasure,
    Measure.toSphere_apply' _ (measurable_subtype_coe measurableSet_closedBall),
    finrank_euclideanSpace_fin, Subtype.image_preimage_coe]

lemma nr_cone_vol (n : ℕ) {η : E n} (hη : ‖η‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((⌊1 / (2 * t)⌋₊ + 1 : ℕ) : ℝ≥0∞) * volume (ball (0 : E n) (t / 8)) ≤
      volume (Set.Ioo (0 : ℝ) 1 • (sphere (0 : E n) 1 ∩ closedBall η t)) := by
  set m := ⌊1 / (2 * t)⌋₊
  set s : ℕ → ℝ := fun j => 1 / 2 + j * t / 2 with hs
  have hm : (m : ℝ) * t ≤ 1 / 2 := by
    have := Nat.floor_le (a := 1 / (2 * t)) (by positivity)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hsb : ∀ j ∈ Finset.range (m + 1), 1 / 2 ≤ s j ∧ s j ≤ 3 / 4 := by
    intro j hj
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have : (j : ℝ) * t ≤ m * t := mul_le_mul_of_nonneg_right hj' ht0.le
    constructor
    · simp only [hs]; have : 0 ≤ (j : ℝ) * t := by positivity
      linarith
    · simp only [hs]; linarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m + 1)))
      (fun j => ball (s j • η) (t / 8)) := by
    intro i _ j _ hij
    apply ball_disjoint_ball
    rw [dist_eq_norm, ← sub_smul, norm_smul, hη, mul_one, Real.norm_eq_abs]
    have e : s i - s j = ((i : ℝ) - j) * (t / 2) := by simp only [hs]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < t / 2)]
    have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    nlinarith
  calc ((m + 1 : ℕ) : ℝ≥0∞) * volume (ball (0 : E n) (t / 8))
      = ∑ j ∈ Finset.range (m + 1), volume (ball (s j • η) (t / 8)) := by
        simp only [Measure.addHaar_ball_center, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ = volume (⋃ j ∈ Finset.range (m + 1), ball (s j • η) (t / 8)) :=
        (measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)).symm
    _ ≤ _ := measure_mono (Set.iUnion₂_subset fun j hj =>
        nr_ball_sub_cone n hη ht0 (hsb j hj).1 (hsb j hj).2 ht1)

lemma nr_cap (n : ℕ) (hn : 2 ≤ n) : ∃ c > 0, ∀ η : E n, ‖η‖ = 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
    c * t ^ (n - 1) ≤ (nr_mu n).real (closedBall η t) := by
  have : Nontrivial (E n) := by
    have : 0 < Module.finrank ℝ (E n) := by rw [finrank_euclideanSpace_fin]; omega
    exact Module.nontrivial_of_finrank_pos this
  set V := (volume : Measure (E n)).real (ball 0 1)
  have hV : 0 < V := by
    exact ENNReal.toReal_pos (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne
  refine ⟨n * V / (2 * 8 ^ n), by positivity, fun η hη t ht0 ht1 => ?_⟩
  set m := ⌊1 / (2 * t)⌋₊
  have hm : 1 / (2 * t) ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hfin : volume (Set.Ioo (0 : ℝ) 1 • (sphere (0 : E n) 1 ∩ closedBall η t)) ≠ ⊤ := by
    have h := measure_ne_top (nr_mu n) (closedBall η t)
    rw [nr_mu_closedBall] at h
    intro htop; apply h; rw [htop, ENNReal.mul_top (by exact_mod_cast (show n ≠ 0 by omega))]
  have key := ENNReal.toReal_mono hfin (nr_cone_vol n hη ht0 ht1)
  rw [ENNReal.toReal_mul, Measure.addHaar_ball _ _ (by positivity), finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at key
  change _ * (_ * V) ≤ _ at key
  rw [measureReal_def, nr_mu_closedBall, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast] at key ⊢
  push_cast at key
  have hn1 : t ^ n = t * t ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e : n * V / (2 * 8 ^ n) * t ^ (n - 1) = n * ((1 / (2 * t)) * ((t / 8) ^ n * V)) := by
    rw [div_pow, hn1]; field_simp
  rw [e]
  gcongr
  calc 1 / (2 * t) * ((t / 8) ^ n * V) ≤ ((m : ℝ) + 1) * ((t / 8) ^ n * V) := by gcongr
    _ ≤ _ := key


lemma nr_M_pos (n : ℕ) (hn : 1 ≤ n) : 0 < nr_M n := by
  have : Nontrivial (E n) := by
    have : 0 < Module.finrank ℝ (E n) := by rw [finrank_euclideanSpace_fin]; omega
    exact Module.nontrivial_of_finrank_pos this
  rw [nr_M, measureReal_def, nr_mu, Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ, sphereMeasure, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  exact ENNReal.toReal_pos (mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
    (measure_ball_pos _ _ one_pos).ne')
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) measure_ball_lt_top.ne)

lemma nr_gauss_lower (n : ℕ) (hn : 2 ≤ n) :
    ∃ c > 0, ∀ r : ℝ, 1 ≤ r → c * r ≤ ∫ x, nr_G n r x * ‖nr_F n x‖ ^ 2 := by
  obtain ⟨c, hc, hcap⟩ := nr_cap n hn
  have hM := nr_M_pos n (by omega)
  refine ⟨nr_M n * (c * Real.exp (-Real.pi)), by positivity, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  rw [nr_gauss_identity n hr0]
  set k : E n × E n → ℝ := fun z => r ^ n * Real.exp (-(Real.pi * r ^ 2) * ‖z.2 - z.1‖ ^ 2)
    with hk_def
  have hkb : ∀ z, ‖k z‖ ≤ r ^ n := by
    intro z
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ Real.pi * r ^ 2 * ‖z.2 - z.1‖ ^ 2 := by positivity
    linarith
  have hkc : Continuous k := by
    simp only [hk_def]; fun_prop
  have hk : Integrable k ((nr_mu n).prod (nr_mu n)) :=
    Integrable.mono' (integrable_const (r ^ n)) hkc.aestronglyMeasurable (ae_of_all _ hkb)
  have hinner : ∀ᵐ ξ ∂(nr_mu n), c * Real.exp (-Real.pi) * r ≤ ∫ η, k (ξ, η) ∂(nr_mu n) := by
    filter_upwards [nr_mu_ae n] with ξ hξ
    have h1 := hcap ξ hξ (1 / r) (by positivity) (by rw [div_le_one hr0]; exact hr)
    have hslice : Integrable (fun η => k (ξ, η)) (nr_mu n) :=
      Integrable.mono' (integrable_const (r ^ n))
        (hkc.comp (Continuous.prodMk_right ξ)).aestronglyMeasurable
        (ae_of_all _ fun η => hkb _)
    have hind : ∫ η, (closedBall ξ (1 / r)).indicator (fun _ => r ^ n * Real.exp (-Real.pi)) η
        ∂(nr_mu n) ≤ ∫ η, k (ξ, η) ∂(nr_mu n) := by
      refine integral_mono ((integrable_const _).indicator measurableSet_closedBall) hslice
        (fun η => ?_)
      by_cases hη : η ∈ closedBall ξ (1 / r)
      · rw [Set.indicator_of_mem hη]
        simp only [hk_def]
        gcongr
        rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hr0] at hη
        have h0 : 0 ≤ ‖η - ξ‖ * r := by positivity
        have : (‖η - ξ‖ * r) ^ 2 ≤ 1 := by nlinarith
        nlinarith [Real.pi_pos]
      · rw [Set.indicator_of_notMem hη]
        simp only [hk_def]; positivity
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul] at hind
    have hrn : r ^ n = r * r ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have e : c * Real.exp (-Real.pi) * r =
        c * (1 / r) ^ (n - 1) * (r ^ n * Real.exp (-Real.pi)) := by
      rw [hrn, one_div_pow]; field_simp
    rw [e]
    refine le_trans ?_ hind
    gcongr
  calc nr_M n * (c * Real.exp (-Real.pi)) * r = ∫ ξ, c * Real.exp (-Real.pi) * r ∂(nr_mu n) := by
        rw [integral_const, smul_eq_mul, nr_M]; ring
    _ ≤ ∫ ξ, ∫ η, k (ξ, η) ∂(nr_mu n) ∂(nr_mu n) :=
        integral_mono_ae (integrable_const _) hk.integral_prod_left hinner


/-! ### The weights -/

/-- One summand `2^{-(k+1)} G_{2^k}` of the weight. -/
noncomputable def nr_f (n : ℕ) (k : ℕ) (x : E n) : ℝ := (1 / 2 : ℝ) ^ (k + 1) * nr_G n (2 ^ k) x

/-- The weight `w_K = ∑_{k<K} 2^{-(k+1)} G_{2^k}`. -/
noncomputable def nr_w (n : ℕ) (K : ℕ) (x : E n) : ℝ := ∑ k ∈ Finset.range K, nr_f n k x

/-- Coefficients for the multinomial bound. -/
noncomputable def nr_c (k m : ℕ) : ℝ := if m ≤ k then (1 / 2 : ℝ) ^ (k - m + 1) else 0

lemma nr_c_nonneg (k m : ℕ) : 0 ≤ nr_c k m := by
  unfold nr_c; split_ifs <;> positivity

lemma nr_geom (m K : ℕ) : ∑ k ∈ Finset.range K, nr_c k m + (1 / 2 : ℝ) ^ (K - m) = 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases h : m ≤ K
    · have e : K + 1 - m = K - m + 1 := by omega
      rw [nr_c, if_pos h, e, pow_succ]
      linarith
    · have e : K + 1 - m = 0 := by omega
      have e' : K - m = 0 := by omega
      rw [nr_c, if_neg h, e]
      rw [e'] at ih
      linarith

lemma nr_geom_le (m K : ℕ) : ∑ k ∈ Finset.range K, nr_c k m ≤ 1 := by
  have := nr_geom m K
  have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K - m) := by positivity
  linarith

lemma nr_G_le_one (n : ℕ) (r : ℝ) (x : E n) : nr_G n r x ≤ 1 := by
  rw [nr_G, Real.exp_le_one_iff]
  have : 0 ≤ Real.pi / r ^ 2 * ‖x‖ ^ 2 := by positivity
  linarith

lemma nr_w_nonneg (n K : ℕ) (x : E n) : 0 ≤ nr_w n K x :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity) (nr_G_nonneg _ _ _))

lemma nr_w_le_one (n K : ℕ) (x : E n) : nr_w n K x ≤ 1 := by
  calc nr_w n K x ≤ ∑ k ∈ Finset.range K, nr_c k 0 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [nr_f, nr_c, if_pos (Nat.zero_le k), Nat.sub_zero]
        exact mul_le_of_le_one_right (by positivity) (nr_G_le_one _ _ _)
    _ ≤ 1 := nr_geom_le 0 K

lemma nr_gauss_contDiff (n : ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (fun x : E n => Real.exp (-b * ‖x‖ ^ 2)) :=
  Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))

lemma nr_w_contDiff (n K : ℕ) : ContDiff ℝ ∞ (nr_w n K) := by
  unfold nr_w nr_f nr_G
  refine ContDiff.sum (fun k _ => contDiff_const.mul ?_)
  exact nr_gauss_contDiff n _

lemma nr_gauss_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E n => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E n)
    (b := (b : ℂ)) (by simp only [Complex.ofReal_re]; positivity) 0 0
  refine h.norm.congr (ae_of_all _ fun x => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

lemma nr_f_integrable (n k : ℕ) : Integrable (nr_f n k) :=
  (nr_G_integrable n (by positivity)).const_mul _

lemma nr_w_integrable (n K : ℕ) : Integrable (nr_w n K) := by
  unfold nr_w
  exact integrable_finsetSum _ (fun k _ => nr_f_integrable n k)

lemma nr_w_lower (n : ℕ) (hn : 2 ≤ n) :
    ∃ c > 0, ∀ K : ℕ, c * K ≤ ∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2 := by
  obtain ⟨c, hc, hlow⟩ := nr_gauss_lower n hn
  refine ⟨c / 2, by positivity, fun K => ?_⟩
  have e : ∀ x, nr_w n K x * ‖nr_F n x‖ ^ 2 =
      ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ (k + 1) * (nr_G n (2 ^ k) x * ‖nr_F n x‖ ^ 2) := by
    intro x; rw [nr_w, Finset.sum_mul]; congr 1; ext k; rw [nr_f]; ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun k _ =>
    (nr_wF_integrable n (nr_G_integrable n (by positivity))).const_mul _)]
  simp_rw [integral_const_mul]
  calc c / 2 * K = ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ (k + 1) * (c * 2 ^ k) := by
        rw [Finset.sum_congr rfl (g := fun _ => c / 2)]
        · simp [mul_comm]
        · intro k _; rw [pow_succ]; field_simp; rw [← mul_pow]; norm_num
    _ ≤ _ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        gcongr
        exact hlow _ (one_le_pow₀ (by norm_num))

lemma nr_coef (k m : ℕ) (h : m ≤ k) : (1 / 2 : ℝ) ^ (k + 1) * 2 ^ m = nr_c k m := by
  rw [nr_c, if_pos h]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show m + d - m + 1 = d + 1 by omega, show m + d + 1 = m + (d + 1) by ring, pow_add]
  rw [mul_comm, ← mul_assoc, ← mul_pow]; norm_num

lemma nr_prod_integral (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (κ : Fin n → ℕ) (hκ : ∀ i, κ i < K) :
    Integrable (fun x => ∏ i, nr_f n (κ i) x) ∧
      ∫ x, ∏ i, nr_f n (κ i) x ≤ ∑ m ∈ Finset.range K, ∏ i, nr_c (κ i) m := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩
  set b := ∑ i, Real.pi / ((2 : ℝ) ^ (κ i)) ^ 2 with hb_def
  have hb : 0 < b := Finset.sum_pos (fun i _ => by positivity) hne
  have hprod : ∀ x, ∏ i, nr_f n (κ i) x =
      (∏ i, (1 / 2 : ℝ) ^ (κ i + 1)) * Real.exp (-b * ‖x‖ ^ 2) := by
    intro x
    simp only [nr_f, nr_G]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    rw [hb_def, ← Finset.sum_neg_distrib, Finset.sum_mul]
  simp_rw [hprod]
  refine ⟨(nr_gauss_integrable n hb).const_mul _, ?_⟩
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ κ hne
  have hbj : Real.pi / ((2 : ℝ) ^ (κ j)) ^ 2 ≤ b :=
    Finset.single_le_sum (f := fun i => Real.pi / ((2 : ℝ) ^ (κ i)) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j)
  have h1 : Real.pi / b ≤ ((2 : ℝ) ^ (κ j)) ^ 2 := by
    rw [div_le_iff₀ hb]
    rw [div_le_iff₀ (by positivity)] at hbj
    linarith
  have h2 : (Real.pi / b) ^ ((n : ℝ) / 2) ≤ ((2 : ℝ) ^ (κ j)) ^ n := by
    rw [← nr_rpow_half n (by positivity : (0 : ℝ) < 2 ^ (κ j))]
    exact Real.rpow_le_rpow (by positivity) h1 (by positivity)
  calc (∏ i, (1 / 2 : ℝ) ^ (κ i + 1)) * (Real.pi / b) ^ ((n : ℝ) / 2)
      ≤ (∏ i, (1 / 2 : ℝ) ^ (κ i + 1)) * ((2 : ℝ) ^ (κ j)) ^ n := by gcongr
    _ = ∏ i, nr_c (κ i) (κ j) := by
        have hc : ((2 : ℝ) ^ (κ j)) ^ n = ∏ _i : Fin n, (2 : ℝ) ^ (κ j) := by
          simp [Finset.prod_const]
        rw [hc, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun i _ => nr_coef _ _ (hj i (Finset.mem_univ i)))
    _ ≤ _ := Finset.single_le_sum (f := fun m => ∏ i, nr_c (κ i) m)
        (fun m _ => Finset.prod_nonneg (fun i _ => nr_c_nonneg _ _))
        (Finset.mem_range.2 (hκ j))

lemma nr_w_pow (n : ℕ) (hn : 1 ≤ n) (K : ℕ) :
    Integrable (fun x => nr_w n K x ^ n) ∧ ∫ x, nr_w n K x ^ n ≤ K := by
  have hexp : ∀ x, nr_w n K x ^ n = ∑ κ ∈ Fintype.piFinset (fun _ : Fin n => Finset.range K),
      ∏ i, nr_f n (κ i) x := by
    intro x
    have : nr_w n K x ^ n = ∏ _i : Fin n, nr_w n K x := by simp [Finset.prod_const]
    rw [this, nr_w, Finset.prod_univ_sum]
  have hmem : ∀ κ ∈ Fintype.piFinset (fun _ : Fin n => Finset.range K), ∀ i, κ i < K :=
    fun κ hκ i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hκ i)
  simp_rw [hexp]
  refine ⟨integrable_finsetSum _ (fun κ hκ => (nr_prod_integral n hn K κ (hmem κ hκ)).1), ?_⟩
  rw [integral_finsetSum _ (fun κ hκ => (nr_prod_integral n hn K κ (hmem κ hκ)).1)]
  calc ∑ κ ∈ Fintype.piFinset (fun _ : Fin n => Finset.range K), ∫ x, ∏ i, nr_f n (κ i) x
      ≤ ∑ κ ∈ Fintype.piFinset (fun _ : Fin n => Finset.range K),
          ∑ m ∈ Finset.range K, ∏ i, nr_c (κ i) m :=
        Finset.sum_le_sum (fun κ hκ => (nr_prod_integral n hn K κ (hmem κ hκ)).2)
    _ = ∑ m ∈ Finset.range K, ∏ _i : Fin n, ∑ k ∈ Finset.range K, nr_c k m := by
        rw [Finset.sum_comm]
        congr 1; ext m
        rw [Finset.prod_univ_sum]
    _ ≤ ∑ m ∈ Finset.range K, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact Finset.prod_le_one (fun i _ => Finset.sum_nonneg (fun k _ => nr_c_nonneg _ _))
          (fun i _ => nr_geom_le m K)
    _ = K := by simp


/-! ### Lᵖ bounds of `w F` -/

lemma nr_norm_wF (n : ℕ) {w : E n → ℝ} (hw0 : ∀ x, 0 ≤ w x) (x : E n) :
    ‖(w x : ℂ) * nr_F n x‖ = w x * ‖nr_F n x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 x)]

lemma nr_pow_split {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 < P) :
    (a * b) ^ P = (a * b ^ 2) ^ (P / 2) * a ^ (P / 2) := by
  rw [Real.mul_rpow ha hb, Real.mul_rpow ha (sq_nonneg b), ← Real.rpow_natCast b 2,
    ← Real.rpow_mul hb]
  have h1 : a ^ P = a ^ (P / 2) * a ^ (P / 2) := by
    rw [← Real.rpow_add' ha (by linarith)]; ring_nf
  have h2 : ((2 : ℕ) : ℝ) * (P / 2) = P := by push_cast; ring
  rw [h1, h2]; ring

lemma nr_lt2 (n : ℕ) (hn : 1 ≤ n) (K : ℕ) {P : ℝ} (hP1 : 1 < P) (hP2 : P < 2)
    (hq : (n : ℝ) ≤ P / (2 - P)) :
    eLpNorm (fun x => (nr_w n K x : ℂ) * nr_F n x) (ENNReal.ofReal P) volume ≤
      ENNReal.ofReal (((∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2) ^ (P / 2) *
        (∫ x, nr_w n K x ^ n) ^ ((2 - P) / 2)) ^ (1 / P)) := by
  have hw0 := nr_w_nonneg n K
  have hw1 := nr_w_le_one n K
  have hP0 : 0 < P := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hP0.le]
  set u : E n → ℝ := fun x => (nr_w n K x * ‖nr_F n x‖ ^ 2) ^ (P / 2) with hu
  set v : E n → ℝ := fun x => nr_w n K x ^ (P / 2) with hv
  have hpt : ∀ x, ‖(nr_w n K x : ℂ) * nr_F n x‖ₑ ^ P = ENNReal.ofReal (u x) * ENNReal.ofReal (v x) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le,
      ← ENNReal.ofReal_mul (by positivity [hw0 x])]
    congr 1
    rw [nr_norm_wF n hw0 x, hu, hv]
    exact nr_pow_split (hw0 x) (norm_nonneg _) hP0
  simp_rw [hpt]
  have hpq : (2 / P).HolderConjugate (2 / (2 - P)) := by
    have := Real.holderConjugate_one_div (a := P / 2) (b := (2 - P) / 2) (by linarith)
      (by linarith) (by ring)
    simpa only [one_div_div] using this
  have hu_c : Continuous u := by
    simp only [hu]
    exact (((nr_w_contDiff n K).continuous.mul
      ((nr_F_continuous n).norm.pow 2))).rpow_const (fun _ => Or.inr (by positivity))
  have hv_c : Continuous v := by
    simp only [hv]
    exact (nr_w_contDiff n K).continuous.rpow_const (fun _ => Or.inr (by positivity))
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    hu_c.measurable.ennreal_ofReal.aemeasurable hv_c.measurable.ennreal_ofReal.aemeasurable
  have e1 : ∫⁻ x, ENNReal.ofReal (u x) ^ (2 / P) =
      ENNReal.ofReal (∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (nr_wF_integrable n (nr_w_integrable n K))
      (ae_of_all _ (fun x => by have := hw0 x; positivity))]
    congr 1; ext x
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity [hw0 x]) (by positivity), hu]
    simp only
    rw [← Real.rpow_mul (by positivity [hw0 x])]
    rw [show P / 2 * (2 / P) = 1 by field_simp, Real.rpow_one]
  have e2 : ∫⁻ x, ENNReal.ofReal (v x) ^ (2 / (2 - P)) ≤
      ENNReal.ofReal (∫ x, nr_w n K x ^ n) := by
    rw [ofReal_integral_eq_lintegral_ofReal (nr_w_pow n hn K).1
      (ae_of_all _ (fun x => by have := hw0 x; positivity))]
    refine lintegral_mono (fun x => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity [hw0 x]) (by apply div_nonneg <;> linarith), hv]
    simp only
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.rpow_mul (hw0 x), ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge' (hw0 x) (hw1 x) (by positivity) ?_
    rw [show P / 2 * (2 / (2 - P)) = P / (2 - P) by field_simp]
    exact hq
  have h2P : 0 ≤ (2 - P) / 2 := by linarith
  calc (∫⁻ x, ENNReal.ofReal (u x) * ENNReal.ofReal (v x)) ^ (1 / P)
      ≤ ((∫⁻ x, ENNReal.ofReal (u x) ^ (2 / P)) ^ (1 / (2 / P)) *
          (∫⁻ x, ENNReal.ofReal (v x) ^ (2 / (2 - P))) ^ (1 / (2 / (2 - P)))) ^ (1 / P) := by
        gcongr
        exact hH
    _ ≤ (ENNReal.ofReal (∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2) ^ (P / 2) *
          ENNReal.ofReal (∫ x, nr_w n K x ^ n) ^ ((2 - P) / 2)) ^ (1 / P) := by
        rw [e1, one_div_div, one_div_div]
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun x => by
            have := hw0 x; positivity)) (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun x => by
            have := hw0 x; positivity)) h2P,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg (fun x => by
            have := hw0 x; positivity)) _),
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg (integral_nonneg
            (fun x => by have := hw0 x; positivity)) _) (Real.rpow_nonneg (integral_nonneg
            (fun x => by have := hw0 x; positivity)) _)) (by positivity)]

lemma nr_ge2 (n : ℕ) (K : ℕ) {P : ℝ} (hP : 2 ≤ P) :
    eLpNorm (fun x => (nr_w n K x : ℂ) * nr_F n x) (ENNReal.ofReal P) volume ≤
      ENNReal.ofReal ((nr_M n ^ (P - 2) * ∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2) ^ (1 / P)) := by
  have hw0 := nr_w_nonneg n K
  have hw1 := nr_w_le_one n K
  have hP0 : 0 < P := by linarith
  have hM0 : 0 ≤ nr_M n := (norm_nonneg _).trans (nr_F_norm_le n 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hP0.le]
  have hL0 : 0 ≤ ∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2 :=
    integral_nonneg (fun x => by have := hw0 x; positivity)
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  gcongr
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
    ((nr_wF_integrable n (nr_w_integrable n K)).const_mul _)
    (ae_of_all _ (fun x => by have := hw0 x; positivity))]
  refine lintegral_mono (fun x => ?_)
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le]
  apply ENNReal.ofReal_le_ofReal
  rw [nr_norm_wF n hw0 x]
  have h0 := hw0 x
  have hF := nr_F_norm_le n x
  have ht : nr_w n K x * ‖nr_F n x‖ ≤ nr_M n := by
    calc nr_w n K x * ‖nr_F n x‖ ≤ 1 * nr_M n := by gcongr; exact hw1 x
      _ = _ := one_mul _
  have ht0 : 0 ≤ nr_w n K x * ‖nr_F n x‖ := by positivity
  rw [show P = (P - 2) + (2 : ℕ) by push_cast; ring, Real.rpow_add' ht0 (by push_cast; linarith),
    Real.rpow_natCast]
  have hsq : (nr_w n K x * ‖nr_F n x‖) ^ 2 ≤ nr_w n K x * ‖nr_F n x‖ ^ 2 := by
    rw [mul_pow]
    have : nr_w n K x ^ 2 ≤ nr_w n K x := by nlinarith [hw1 x]
    gcongr
  have hpow : (nr_w n K x * ‖nr_F n x‖) ^ (P - 2) ≤ nr_M n ^ (P - 2) :=
    Real.rpow_le_rpow ht0 ht (by linarith)
  calc (nr_w n K x * ‖nr_F n x‖) ^ (P - 2) * (nr_w n K x * ‖nr_F n x‖) ^ 2
      ≤ nr_M n ^ (P - 2) * (nr_w n K x * ‖nr_F n x‖ ^ 2) := by
        gcongr
    _ = _ := by push_cast; ring_nf

lemma nr_top (n : ℕ) (K : ℕ) :
    eLpNorm (fun x => (nr_w n K x : ℂ) * nr_F n x) ⊤ volume ≤ ENNReal.ofReal (nr_M n) := by
  rw [eLpNorm_exponent_top]
  refine eLpNormEssSup_le_of_ae_bound (ae_of_all _ (fun x => ?_))
  rw [nr_norm_wF n (nr_w_nonneg n K) x]
  calc nr_w n K x * ‖nr_F n x‖ ≤ 1 * nr_M n := by
        gcongr
        · exact nr_w_le_one n K x
        · exact nr_F_norm_le n x
    _ = _ := one_mul _

/-! ### Real-number endgame -/

lemma nr_bound_self {L A s : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hs1 : s < 1)
    (h : L ≤ A * L ^ s) : L ≤ A ^ (1 / (1 - s)) := by
  rcases hL.eq_or_lt with rfl | hLpos
  · exact Real.rpow_nonneg hA _
  have hLs : 0 < L ^ s := Real.rpow_pos_of_pos hLpos s
  have e : L = L ^ s * L ^ (1 - s) := by
    rw [← Real.rpow_add hLpos]; simp
  have h1 : L ^ (1 - s) ≤ A := by
    have : L ^ s * L ^ (1 - s) ≤ L ^ s * A := by rw [← e, mul_comm]; exact h
    exact le_of_mul_le_mul_left this hLs
  calc L = (L ^ (1 - s)) ^ (1 / (1 - s)) := by
        rw [← Real.rpow_mul hL, mul_one_div_cancel (by linarith), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hL _) h1 (by
        have : 0 < 1 - s := by linarith
        positivity)

lemma nr_contra {c B θ : ℝ} (hc : 0 < c) (hθ : θ < 1)
    (h : ∀ K : ℕ, 1 ≤ K → c * K ≤ B * (K : ℝ) ^ θ) : False := by
  have ht : Tendsto (fun K : ℕ => (K : ℝ) ^ (1 - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK1, hK2⟩ := ((ht.eventually_gt_atTop (B / c)).and (eventually_ge_atTop 1)).exists
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK2
  have hθpos : 0 < (K : ℝ) ^ θ := Real.rpow_pos_of_pos hKpos θ
  have e : (K : ℝ) ^ (1 - θ) * (K : ℝ) ^ θ = K := by
    rw [← Real.rpow_add hKpos]; simp
  have h1 := h K hK2
  have h2 : c * (B / c) = B := by field_simp
  have h3 := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hK1 hc) hθpos
  rw [h2, mul_assoc, e] at h3
  linarith


end TaoBR.NotRestr

namespace TaoBR

open NotRestr in
theorem not_restr_zero_of_le_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal (2 * n / (n + 1)) ≤ p) : ¬ Restr n p 0 := by
  intro h
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcrit1 : 1 < 2 * (n : ℝ) / (n + 1) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hp1 : 1 ≤ p := le_trans (by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hcrit1.le) hp
  obtain ⟨K₀, hK₀, hdual⟩ := nr_dual n hp1 h
  obtain ⟨c, hc, hlow⟩ := nr_w_lower n hn
  set k₀ := K₀.toReal with hk₀_def
  have hk₀ : K₀ = ENNReal.ofReal k₀ := (ENNReal.ofReal_toReal hK₀).symm
  have hk0 : 0 ≤ k₀ := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ nr_M n := (norm_nonneg _).trans (nr_F_norm_le n 0)
  have hL : ∀ K : ℕ, ENNReal.ofReal (∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2) ≤
      ENNReal.ofReal k₀ * eLpNorm (fun x => (nr_w n K x : ℂ) * nr_F n x) p volume := by
    intro K
    rw [← hk₀]
    exact hdual _ (nr_w_contDiff n K) (nr_w_integrable n K) (nr_w_nonneg n K)
  have hL0 : ∀ K : ℕ, 0 ≤ ∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2 := fun K =>
    integral_nonneg (fun x => by have := nr_w_nonneg n K x; positivity)
  rcases eq_or_ne p ⊤ with rfl | hpt
  · refine nr_contra (c := c) (B := k₀ * nr_M n) (θ := 0) hc (by norm_num) (fun K _ => ?_)
    have h1 := (hL K).trans (mul_le_mul' le_rfl (nr_top n K))
    rw [← ENNReal.ofReal_mul hk0, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    rw [Real.rpow_zero, mul_one]
    exact (hlow K).trans h1
  set P := p.toReal with hP_def
  have hpP : p = ENNReal.ofReal P := (ENNReal.ofReal_toReal hpt).symm
  have hPc : 2 * (n : ℝ) / (n + 1) ≤ P := by
    have := ENNReal.toReal_mono hpt hp
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hP1 : 1 < P := lt_of_lt_of_le hcrit1 hPc
  have hP0 : 0 < P := by linarith
  rw [hpP] at hL
  rcases lt_or_ge P 2 with hP2 | hP2
  · have hq : (n : ℝ) ≤ P / (2 - P) := by
      rw [le_div_iff₀ (by linarith)]
      rw [div_le_iff₀ (by positivity)] at hPc
      nlinarith
    refine nr_contra (c := c) (B := k₀ ^ 2) (θ := (2 - P) / P) hc
      (by rw [div_lt_one hP0]; linarith) (fun K hK => ?_)
    set L := ∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2 with hL_def
    set A := ∫ x, nr_w n K x ^ n with hA_def
    have hA : A ≤ K := (nr_w_pow n (by omega) K).2
    have hA0 : 0 ≤ A := integral_nonneg (fun x => pow_nonneg (nr_w_nonneg n K x) n)
    have h1 := (hL K).trans (mul_le_mul' le_rfl (nr_lt2 n (by omega) K hP1 hP2 hq))
    rw [← ENNReal.ofReal_mul hk0, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk0
      (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (hL0 K) _) (Real.rpow_nonneg hA0 _)) _))]
      at h1
    have h2 : L ≤ (k₀ * A ^ ((2 - P) / (2 * P))) * L ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (hL0 K) _) (Real.rpow_nonneg hA0 _),
        ← Real.rpow_mul (hL0 K), ← Real.rpow_mul hA0] at h1
      have e1 : P / 2 * (1 / P) = 1 / 2 := by field_simp
      have e2 : (2 - P) / 2 * (1 / P) = (2 - P) / (2 * P) := by field_simp
      rw [e1, e2] at h1
      linarith
    have h3 := nr_bound_self (hL0 K) (by positivity) (by norm_num : (1 / 2 : ℝ) < 1) h2
    have e3 : (1 : ℝ) / (1 - 1 / 2) = (2 : ℕ) := by norm_num
    rw [e3, Real.rpow_natCast, mul_pow, ← Real.rpow_mul_natCast hA0] at h3
    have e4 : (2 - P) / (2 * P) * ((2 : ℕ) : ℝ) = (2 - P) / P := by push_cast; field_simp
    rw [e4] at h3
    calc c * K ≤ L := hlow K
      _ ≤ k₀ ^ 2 * A ^ ((2 - P) / P) := h3
      _ ≤ k₀ ^ 2 * (K : ℝ) ^ ((2 - P) / P) := by
        gcongr
  · refine nr_contra (c := c) (B := (k₀ * nr_M n ^ ((P - 2) / P)) ^ (1 / (1 - 1 / P)))
      (θ := 0) hc (by norm_num) (fun K _ => ?_)
    set L := ∫ x, nr_w n K x * ‖nr_F n x‖ ^ 2 with hL_def
    have h1 := (hL K).trans (mul_le_mul' le_rfl (nr_ge2 n K hP2))
    rw [← ENNReal.ofReal_mul hk0, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk0
      (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hM0 _) (hL0 K)) _))] at h1
    have h2 : L ≤ (k₀ * nr_M n ^ ((P - 2) / P)) * L ^ (1 / P) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hM0 _) (hL0 K), ← Real.rpow_mul hM0] at h1
      have e1 : (P - 2) * (1 / P) = (P - 2) / P := by field_simp
      rw [e1] at h1
      linarith
    have h3 := nr_bound_self (hL0 K) (by positivity)
      (by rw [div_lt_one hP0]; exact hP1) h2
    rw [Real.rpow_zero, mul_one]
    exact (hlow K).trans h3

end TaoBR

section
open scoped ENNReal
open TaoBR

theorem solution (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal (2 * n / (n + 1)) ≤ p) : ¬ Restr n p 0 :=
  TaoBR.not_restr_zero_of_le_dev n hn p hp

end
