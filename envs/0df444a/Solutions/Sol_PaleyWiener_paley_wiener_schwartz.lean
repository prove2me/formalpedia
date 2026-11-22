-- Prove2me | solution 1 for PaleyWiener.paley_wiener_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T19:15:38.833798+00:00
-- url     : https://prove2.me/submissions/3ce417e1-5ad8-4bf4-bce3-c9473ea552ce

import Mathlib

set_option autoImplicit false

namespace PWSHelp

open Complex MeasureTheory Filter Topology Set
open scoped ContDiff FourierTransform Real

lemma norm_kernel (z : ℂ) (x : ℝ) : ‖cexp (-(I * z * x))‖ = Real.exp (z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma kernel_bound (z : ℂ) (x A : ℝ) (hx : x ∈ Icc (-A) A) :
    ‖cexp (-(I * z * x))‖ ≤ Real.exp (A * |z.im|) := by
  rw [norm_kernel]
  apply Real.exp_le_exp.mpr
  have : |x| ≤ A := abs_le.mpr hx
  calc z.im * x ≤ |z.im * x| := le_abs_self _
    _ = |z.im| * |x| := abs_mul _ _
    _ ≤ |z.im| * A := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = A * |z.im| := mul_comm _ _

lemma integral_bound (ψ : ℝ → ℂ) (A : ℝ) (hψ : Continuous ψ) (hs : tsupport ψ ⊆ Icc (-A) A)
    (z : ℂ) :
    ‖∫ x : ℝ, ψ x * cexp (-(I * z * x))‖ ≤ (∫ x : ℝ, ‖ψ x‖) * Real.exp (A * |z.im|) := by
  have hc : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport ψ) hs
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le
  · exact (hψ.norm.integrable_of_hasCompactSupport hc.norm).mul_const _
  · refine Eventually.of_forall (fun x => ?_)
    rw [norm_mul]
    by_cases hx : x ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_left (kernel_bound z x A (hs hx)) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp

lemma entire (φ : ℝ → ℂ) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Differentiable ℂ (fun z : ℂ => ∫ x : ℝ, φ x * cexp (-(I * z * x))) := by
  intro z₀
  have hcont : ∀ z : ℂ, Continuous (fun x : ℝ => φ x * cexp (-(I * z * x))) := fun z => by
    fun_prop
  have hint : ∀ z : ℂ, Integrable (fun x : ℝ => φ x * cexp (-(I * z * x))) := fun z =>
    (hcont z).integrable_of_hasCompactSupport (hs.mul_right)
  set R := |z₀.im| + 1 with hR
  have hbound_int : Integrable (fun x : ℝ => ‖φ x‖ * (|x| * Real.exp (R * |x|))) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact hs.norm.mul_right
  have hF'c : Continuous (fun x : ℝ => φ x * (-(I * x) * cexp (-(I * z₀ * x)))) := by fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := z₀)
    (F := fun z x => φ x * cexp (-(I * z * x)))
    (F' := fun z x => φ x * (-(I * x) * cexp (-(I * z * x))))
    (bound := fun x : ℝ => ‖φ x‖ * (|x| * Real.exp (R * |x|)))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hint z).aestronglyMeasurable)
    (hint z₀) hF'c.aestronglyMeasurable ?_ hbound_int ?_
  · exact key.2.differentiableAt
  · refine Eventually.of_forall (fun x z hz => ?_)
    rw [norm_mul, norm_mul, norm_neg, norm_mul, norm_I, one_mul, norm_kernel]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have h1 : |z.im| ≤ R := by
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        have := Complex.abs_im_le_norm (z - z₀)
        simpa using this
      have h3 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have h4 : |z.im| ≤ |z₀.im| + |z.im - z₀.im| := by
        have := abs_add_le z₀.im (z.im - z₀.im)
        simpa using this
      linarith
    calc z.im * x ≤ |z.im * x| := le_abs_self _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ R * |x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  · refine Eventually.of_forall (fun x z _ => ?_)
    have h1 : HasDerivAt (fun z : ℂ => -(I * z * x)) (-(I * x)) z := by
      have e : (fun z : ℂ => -(I * z * x)) = fun z => z * (-(I * x)) := by funext w; ring
      rw [e]; exact hasDerivAt_mul_const _
    have h3 := (h1.cexp).const_mul (φ x)
    exact h3.congr_deriv (by ring)

lemma ibp (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (z : ℂ) :
    ∫ x : ℝ, deriv φ x * cexp (-(I * z * x)) = (I * z) * ∫ x : ℝ, φ x * cexp (-(I * z * x)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hd' : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  set u : ℝ → ℂ := fun x => cexp (-(I * z * x)) with hu_def
  have huc : Continuous u := by fun_prop
  have hu : ∀ x : ℝ, HasDerivAt u (-(I * z) * u x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(I * z * (x : ℂ))) (-(I * z)) x := by
      have e : (fun x : ℝ => -(I * z * (x : ℂ))) = fun x : ℝ => (-(I * z)) * (x : ℂ) := by
        funext w; ring
      rw [e]
      have := ((hasDerivAt_id x).ofReal_comp.const_mul (-(I * z)))
      simpa using this
    have := h1.cexp
    exact this.congr_deriv (by simp only [hu_def]; ring)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := u) (v := φ)
    (u' := fun x => -(I * z) * u x) (v' := deriv φ)
    (fun x _ => hu x) (fun x _ => (hd x).hasDerivAt) ?_ ?_ ?_
  · have e1 : (∫ x : ℝ, deriv φ x * u x) = ∫ x : ℝ, u x * deriv φ x := by
      congr 1; ext x; ring
    have e2 : (∫ x : ℝ, -(I * z) * u x * φ x) = -(I * z) * ∫ x : ℝ, φ x * u x := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    change (∫ x : ℝ, deriv φ x * u x) = (I * z) * ∫ x : ℝ, φ x * u x
    rw [e1, key, e2]; ring
  · exact (huc.mul hd').integrable_of_hasCompactSupport hs.deriv.mul_left
  · exact ((continuous_const.mul huc).mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left
  · exact (huc.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left

lemma ibp_iter (N : ℕ) : ∀ (φ : ℝ → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ z : ℂ,
    ∫ x : ℝ, iteratedDeriv N φ x * cexp (-(I * z * x)) =
      (I * z) ^ N * ∫ x : ℝ, φ x * cexp (-(I * z * x)) := by
  induction N with
  | zero => intro φ _ _ z; simp
  | succ n ih =>
    intro φ hφ hs z
    rw [iteratedDeriv_succ', ih (deriv φ) (contDiff_infty_iff_deriv.mp hφ).2 hs.deriv z,
      ibp φ hφ hs z]
    ring

lemma tsupport_iteratedDeriv_subset' (φ : ℝ → ℂ) (N : ℕ) :
    tsupport (iteratedDeriv N φ) ⊆ tsupport φ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

lemma pow_bound (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2 ^ N * (1 + t ^ N) :=
        le_mul_of_one_le_right (by positivity) (by have := pow_nonneg ht N; linarith)
  · calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * t ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr; linarith

lemma forward (A : ℝ) (F : ℂ → ℂ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ Icc (-A) A)
    (hF : ∀ z, F z = ∫ x : ℝ, φ x * cexp (-(I * z * x))) :
    Differentiable ℂ F ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ z : ℂ,
      (1 + ‖z‖) ^ N * ‖F z‖ ≤ C * Real.exp (A * |z.im|) := by
  have hc : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport φ) hs
  have hFeq : F = fun z => ∫ x : ℝ, φ x * cexp (-(I * z * x)) := funext hF
  refine ⟨hFeq ▸ entire φ hφ.continuous hc, fun N => ?_⟩
  refine ⟨2 ^ N * ((∫ x : ℝ, ‖φ x‖) + ∫ x : ℝ, ‖iteratedDeriv N φ x‖), fun z => ?_⟩
  have h0 : ‖F z‖ ≤ (∫ x : ℝ, ‖φ x‖) * Real.exp (A * |z.im|) := by
    rw [hF z]
    exact integral_bound φ A hφ.continuous hs z
  have hN : ‖z‖ ^ N * ‖F z‖ ≤ (∫ x : ℝ, ‖iteratedDeriv N φ x‖) * Real.exp (A * |z.im|) := by
    have := integral_bound (iteratedDeriv N φ) A (hφ.continuous_iteratedDeriv N (by exact_mod_cast le_top))
      ((tsupport_iteratedDeriv_subset' φ N).trans hs) z
    rw [ibp_iter N φ hφ hc z, norm_mul, norm_pow, norm_mul, norm_I, one_mul, ← hF z] at this
    exact this
  have hpow := pow_bound ‖z‖ (norm_nonneg _) N
  calc (1 + ‖z‖) ^ N * ‖F z‖ ≤ 2 ^ N * (1 + ‖z‖ ^ N) * ‖F z‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 2 ^ N * (‖F z‖ + ‖z‖ ^ N * ‖F z‖) := by ring
    _ ≤ 2 ^ N * ((∫ x : ℝ, ‖φ x‖) * Real.exp (A * |z.im|) +
          (∫ x : ℝ, ‖iteratedDeriv N φ x‖) * Real.exp (A * |z.im|)) := by gcongr
    _ = 2 ^ N * ((∫ x : ℝ, ‖φ x‖) + ∫ x : ℝ, ‖iteratedDeriv N φ x‖) *
          Real.exp (A * |z.im|) := by ring

lemma contour_shift (h : ℂ → ℂ) (hd : Differentiable ℂ h) (c M : ℝ)
    (hb : ∀ x y : ℝ, |y| ≤ |c| → ‖h (x + y * I)‖ ≤ M * (1 + x ^ 2)⁻¹) :
    ∫ x : ℝ, h x = ∫ x : ℝ, h (x + c * I) := by
  have hint : ∀ y : ℝ, |y| ≤ |c| → Integrable (fun x : ℝ => h (x + y * I)) := by
    intro y hy
    refine (integrable_inv_one_add_sq.const_mul M).mono' ?_
      (Eventually.of_forall fun x => hb x y hy)
    exact (hd.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hint0 : Integrable (fun x : ℝ => h x) := by simpa using hint 0 (by simp)
  have hintc := hint c le_rfl
  have rect : ∀ T : ℝ, ((∫ x in -T..T, h x) - (∫ x in -T..T, h (x + c * I))) +
      (I • (∫ y in (0:ℝ)..c, h (T + y * I)) - I • (∫ y in (0:ℝ)..c, h (-T + y * I))) = 0 := by
    intro T
    have := integral_boundary_rect_eq_zero_of_differentiableOn h (-T) (T + c * I)
      hd.differentiableOn
    simp at this
    rw [← this]; ring
  have vert : ∀ T : ℝ, ‖∫ y in (0:ℝ)..c, h (T + y * I)‖ ≤ M * (1 + T ^ 2)⁻¹ * |c - 0| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    apply hb
    have := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
    simpa using this
  have tend0 : Tendsto (fun T : ℝ => M * (1 + T ^ 2)⁻¹ * |c - 0|) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      apply tendsto_atTop_add_const_left
      exact tendsto_pow_atTop (by norm_num)
    simpa using (this.const_mul M).mul_const |c - 0|
  have tend0' : Tendsto (fun T : ℝ => M * (1 + (-T) ^ 2)⁻¹ * |c - 0|) atTop (𝓝 0) := by
    simpa using tend0
  have hV1 : Tendsto (fun T : ℝ => ∫ y in (0:ℝ)..c, h (T + y * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) vert tend0
  have hV2 : Tendsto (fun T : ℝ => ∫ y in (0:ℝ)..c, h (-T + y * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) tend0'
    have := vert (-T)
    simpa using this
  have hV : Tendsto (fun T : ℝ => I • (∫ y in (0:ℝ)..c, h (T + y * I)) -
      I • (∫ y in (0:ℝ)..c, h (-T + y * I))) atTop (𝓝 0) := by
    simpa using (hV1.const_smul I).sub (hV2.const_smul I)
  have h1 := intervalIntegral_tendsto_integral hint0 tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral hintc tendsto_neg_atTop_atBot tendsto_id
  have h3 := (h1.sub h2).add hV
  have h4 : Tendsto (fun T : ℝ => ((∫ x in -T..T, h x) - (∫ x in -T..T, h (x + c * I))) +
      (I • (∫ y in (0:ℝ)..c, h (T + y * I)) - I • (∫ y in (0:ℝ)..c, h (-T + y * I))))
      atTop (𝓝 0) := by
    simp only [rect]; exact tendsto_const_nhds
  have := tendsto_nhds_unique h3 h4
  linear_combination this


lemma reverse (A : ℝ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hB : ∀ N : ℕ, ∃ C : ℝ, ∀ z : ℂ, (1 + ‖z‖) ^ N * ‖F z‖ ≤ C * Real.exp (A * |z.im|)) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Icc (-A) A ∧
      ∀ z : ℂ, F z = ∫ x : ℝ, φ x * cexp (-(I * z * x)) := by
  set g : ℝ → ℂ := fun v => F (2 * π * v) with hg_def
  have hgc : Continuous g := hF.continuous.comp (by fun_prop)
  have hgb : ∀ n : ℕ, ∃ C : ℝ, ∀ v : ℝ, ‖v‖ ^ n * ‖g v‖ ≤ C * (1 + v ^ 2)⁻¹ := by
    intro n
    obtain ⟨C, hC⟩ := hB (n + 2)
    refine ⟨C, fun v => ?_⟩
    have h1 := hC (2 * π * v)
    have him : (2 * (π : ℂ) * v).im = 0 := by simp
    have hnorm : ‖(2 * (π : ℂ) * v)‖ = 2 * π * |v| := by
      simp [abs_of_pos Real.pi_pos]
    rw [him, abs_zero, mul_zero, Real.exp_zero, mul_one, hnorm] at h1
    have hv1 : |v| ≤ 1 + 2 * π * |v| := by nlinarith [Real.pi_gt_three, abs_nonneg v]
    have hv2 : 1 + v ^ 2 ≤ (1 + 2 * π * |v|) ^ 2 := by
      have e : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
      have hπ : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
      have hw : |v| ≤ 2 * π * |v| := le_mul_of_one_le_left (abs_nonneg v) hπ
      have hw2 : |v| ^ 2 ≤ (2 * π * |v|) ^ 2 := pow_le_pow_left₀ (abs_nonneg v) hw 2
      have hw0 : 0 ≤ 2 * π * |v| := by positivity
      rw [e]; nlinarith [hw2, hw0]
    have hp : ‖v‖ ^ n * (1 + v ^ 2) ≤ (1 + 2 * π * |v|) ^ (n + 2) := by
      rw [pow_add, Real.norm_eq_abs]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hv1 n) hv2 (by positivity)
        (by positivity)
    have hpos : (0:ℝ) < 1 + v ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖v‖ ^ n * ‖g v‖ * (1 + v ^ 2) = (‖v‖ ^ n * (1 + v ^ 2)) * ‖g v‖ := by ring
      _ ≤ (1 + 2 * π * |v|) ^ (n + 2) * ‖g v‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ C := h1
  have hgint : ∀ n : ℕ, Integrable (fun v : ℝ => ‖v‖ ^ n * ‖g (-v)‖) := by
    intro n
    obtain ⟨C, hC⟩ := hgb n
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      ((continuous_norm.pow n).mul (hgc.comp continuous_neg).norm).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have := hC (-v)
    simpa using this
  have hgI : Integrable g := by
    obtain ⟨C, hC⟩ := hgb 0
    refine (integrable_inv_one_add_sq.const_mul C).mono' hgc.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    simpa using hC v
  set φ : ℝ → ℂ := 𝓕⁻ g with hφ_def
  have hφsmooth : ContDiff ℝ ∞ φ := by
    rw [hφ_def, Real.fourierInv_eq_fourier_comp_neg]
    exact Real.contDiff_fourier (fun n _ => hgint n)
  obtain ⟨C2, hC2⟩ := hB 2
  have hC2nn : 0 ≤ C2 := by
    have h1 := hC2 0
    have h2 : 0 ≤ (1 + ‖(0:ℂ)‖) ^ 2 * ‖F 0‖ := by positivity
    have h3 := Real.exp_pos (A * |(0:ℂ).im|)
    by_contra hneg
    have hneg' : C2 < 0 := lt_of_not_ge hneg
    have := mul_neg_of_neg_of_pos hneg' h3
    linarith
  have hFb : ∀ z : ℂ, ‖F z‖ ≤ C2 * Real.exp (A * |z.im|) * (1 + z.re ^ 2)⁻¹ := by
    intro z
    have h1 := hC2 z
    have h2 : 1 + z.re ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
      have h3 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h4 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
      nlinarith [norm_nonneg z]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖F z‖ * (1 + z.re ^ 2) ≤ ‖F z‖ * (1 + ‖z‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (1 + ‖z‖) ^ 2 * ‖F z‖ := mul_comm _ _
      _ ≤ _ := h1
  have hφzero : ∀ x : ℝ, x ∉ Icc (-A) A → φ x = 0 := by
    intro x hx
    set h : ℂ → ℂ := fun w => cexp (2 * π * I * w * x) * F (2 * π * w) with h_def
    have hd : Differentiable ℂ h := by
      have h1 : Differentiable ℂ (fun w : ℂ => cexp (2 * π * I * w * x)) := by fun_prop
      have h2 : Differentiable ℂ (fun w : ℂ => F (2 * π * w)) := hF.comp (by fun_prop)
      exact h1.mul h2
    have hφx : φ x = ∫ v : ℝ, h v := by
      rw [hφ_def, Real.fourierInv_eq']
      congr 1; ext v
      simp only [smul_eq_mul, h_def, hg_def]
      congr 2
      simp
      ring
    have hpt : ∀ v y : ℝ, ‖h (v + y * I)‖ ≤
        C2 * Real.exp (2 * π * (A * |y| - y * x)) * (1 + v ^ 2)⁻¹ := by
      intro v y
      simp only [h_def]
      rw [norm_mul, Complex.norm_exp]
      have hre : (2 * π * I * (v + y * I) * x).re = -(2 * π * y * x) := by simp
      have hF1 := hFb (2 * π * (v + y * I))
      have him : (2 * (π:ℂ) * (v + y * I)).im = 2 * π * y := by simp
      have hre2 : (2 * (π:ℂ) * (v + y * I)).re = 2 * π * v := by simp
      rw [him, hre2] at hF1
      have hinv : (1 + (2 * π * v) ^ 2)⁻¹ ≤ (1 + v ^ 2)⁻¹ := by
        apply inv_anti₀ (by positivity)
        have : v ^ 2 ≤ (2 * π * v) ^ 2 := by
          have hp : (1:ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
          rw [mul_pow]; nlinarith [sq_nonneg v]
        linarith
      have habs : A * |2 * π * y| = 2 * π * (A * |y|) := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]; ring
      rw [habs] at hF1
      rw [hre]
      calc Real.exp (-(2 * π * y * x)) * ‖F (2 * π * (v + y * I))‖
          ≤ Real.exp (-(2 * π * y * x)) * (C2 * Real.exp (2 * π * (A * |y|)) * (1 + v ^ 2)⁻¹) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact hF1.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
        _ = C2 * Real.exp (2 * π * (A * |y| - y * x)) * (1 + v ^ 2)⁻¹ := by
            rw [show 2 * π * (A * |y| - y * x) = 2 * π * (A * |y|) + -(2 * π * y * x) by ring,
              Real.exp_add]
            ring
    have hshift : ∀ t : ℝ, ‖φ x‖ ≤
        C2 * Real.exp (2 * π * (A * |t| - t * x)) * ∫ v : ℝ, (1 + v ^ 2)⁻¹ := by
      intro t
      have hcs := contour_shift h hd t (C2 * Real.exp (2 * π * (|A| * |t| + |t| * |x|)))
        (fun v y hy => (hpt v y).trans (by
          have e1 : A * |y| ≤ |A| * |t| :=
            (mul_le_mul_of_nonneg_right (le_abs_self A) (abs_nonneg y)).trans
              (mul_le_mul_of_nonneg_left hy (abs_nonneg A))
          have e2 : -(y * x) ≤ |t| * |x| := (neg_le_abs (y * x)).trans (by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right hy (abs_nonneg x))
          have e3 : 2 * π * (A * |y| - y * x) ≤ 2 * π * (|A| * |t| + |t| * |x|) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr e3) hC2nn) (by positivity)))
      rw [hφx, hcs, ← integral_const_mul]
      apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
      exact Eventually.of_forall (fun v => hpt v t)
    obtain ⟨σ, hσ, hσx⟩ : ∃ σ : ℝ, |σ| = 1 ∧ A < σ * x := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · exact ⟨-1, by simp, by linarith⟩
      · exact ⟨1, by simp, by linarith⟩
    set K := ∫ v : ℝ, (1 + v ^ 2)⁻¹
    have hc : 2 * π * (A - σ * x) < 0 := by
      have : A - σ * x < 0 := by linarith
      nlinarith [Real.pi_pos]
    have hlim : Tendsto (fun s : ℝ => C2 * Real.exp (2 * π * (A - σ * x) * s) * K) atTop
        (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc))
      simpa using (this.const_mul C2).mul_const K
    have hle : ∀ᶠ s in atTop, ‖φ x‖ ≤ C2 * Real.exp (2 * π * (A - σ * x) * s) * K := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      have := hshift (σ * s)
      have e : 2 * π * (A * |σ * s| - σ * s * x) = 2 * π * (A - σ * x) * s := by
        rw [abs_mul, hσ, abs_of_nonneg hs]; ring
      rw [e] at this
      exact this
    have := ge_of_tendsto hlim hle
    exact norm_le_zero_iff.mp this
  have hsupp : tsupport φ ⊆ Icc (-A) A :=
    closure_minimal (fun x hx => by
      by_contra hcon
      exact hx (hφzero x hcon)) isClosed_Icc
  have hφcs : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport φ) hsupp
  have hFg : Integrable (𝓕 g) := by
    have e : 𝓕 g = fun w => φ (-w) := by
      funext w
      rw [hφ_def, Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [e]
    exact (hφsmooth.continuous.comp continuous_neg).integrable_of_hasCompactSupport
      (hφcs.comp_homeomorph (Homeomorph.neg ℝ))
  have hinv : ∀ w : ℝ, 𝓕 φ w = g w := fun w =>
    hgI.fourier_fourierInv_eq hFg hgc.continuousAt
  refine ⟨φ, hφsmooth, hsupp, ?_⟩
  have hG : Differentiable ℂ (fun z : ℂ => ∫ x : ℝ, φ x * cexp (-(I * z * x))) :=
    entire φ hφsmooth.continuous hφcs
  have hreal : ∀ ξ : ℝ, F ξ = ∫ x : ℝ, φ x * cexp (-(I * (ξ:ℂ) * x)) := by
    intro ξ
    calc F ξ = g (ξ / (2 * π)) := by
          simp only [hg_def]
          congr 1
          push_cast
          field_simp
      _ = 𝓕 φ (ξ / (2 * π)) := (hinv _).symm
      _ = ∫ x : ℝ, φ x * cexp (-(I * (ξ:ℂ) * x)) := by
          rw [Real.fourier_real_eq_integral_exp_smul]
          congr 1; ext v
          rw [smul_eq_mul, mul_comm]
          congr 2
          push_cast
          field_simp
  have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ),
      F z = (fun z : ℂ => ∫ x : ℝ, φ x * cexp (-(I * z * x))) z := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
    exact ht.frequently (Frequently.of_forall (fun x => hreal x))
  have := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hF.analyticAt z)
    (fun z _ => hG.analyticAt z) hfreq
  intro z
  exact congrFun this z

end PWSHelp

theorem solution (A : ℝ) (F : ℂ → ℂ) :
    (∃ φ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ tsupport φ ⊆ Set.Icc (-A) A ∧
      ∀ z : ℂ, F z = ∫ x : ℝ, φ x * Complex.exp (-(Complex.I * z * x))) ↔
    (Differentiable ℂ F ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ z : ℂ,
      (1 + ‖z‖) ^ N * ‖F z‖ ≤ C * Real.exp (A * |z.im|)) := by
  constructor
  · rintro ⟨φ, hφ, hs, hF⟩
    exact PWSHelp.forward A F φ hφ hs hF
  · rintro ⟨hF, hB⟩
    exact PWSHelp.reverse A F hF hB
