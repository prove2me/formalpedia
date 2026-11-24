-- Prove2me | solution 1 for RoughSurfaceScattering.harmonic_gradient_estimate_C_R3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T10:28:47.253237+00:00
-- url     : https://prove2.me/submissions/a8c5b3a4-070e-4c9b-91be-8be26450df20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_harmonic_radial_mollifier_R3

open MeasureTheory Metric
open RoughSurfaceScattering

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- A smooth radial bump supported in `B(0, ε)`. -/
noncomputable def bump0 (ε : ℝ) (y : R3) : ℝ := Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2)

lemma bump0_contDiff (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (bump0 ε) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

lemma bump0_support (ε : ℝ) (hε : 0 < ε) : Function.support (bump0 ε) ⊆ ball 0 ε := by
  intro y hy
  rw [mem_ball, dist_zero_right]
  by_contra h
  push Not at h
  apply hy
  apply Real.smoothTransition.zero_of_nonpos
  have : 1 ≤ ‖y‖ ^ 2 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hε.le h 2
  linarith

lemma bump0_integral_pos (ε : ℝ) (hε : 0 < ε) : 0 < ∫ y, bump0 ε y := by
  have hcont : Continuous (bump0 ε) := (bump0_contDiff ε (n := 0)).continuous
  have hcs : HasCompactSupport (bump0 ε) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ε)
      ((bump0_support ε hε).trans ball_subset_closedBall)
  have hint : Integrable (bump0 ε) := hcont.integrable_of_hasCompactSupport hcs
  rw [integral_pos_iff_support_of_nonneg (f := bump0 ε)
    (fun y => by simp only [Pi.zero_apply, bump0]; exact Real.smoothTransition.nonneg _) hint]
  have h0 : (0 : R3) ∈ Function.support (bump0 ε) := by
    simp only [Function.mem_support, bump0, norm_zero]
    rw [Real.smoothTransition.one_of_one_le (by norm_num)]; norm_num
  have hopen : IsOpen (Function.support (bump0 ε)) := hcont.isOpen_support
  exact hopen.measure_pos volume ⟨0, h0⟩

/-- The fixed mollifier `φ₁ = c⁻¹ · bump0 1`, supported in `B(0,1)`. -/
noncomputable def phi1 : R3 → ℝ := fun y => (∫ y, bump0 1 y)⁻¹ * bump0 1 y

lemma phi1_contDiff {n : ℕ∞} : ContDiff ℝ n phi1 := contDiff_const.mul (bump0_contDiff 1)

lemma phi1_support : Function.support phi1 ⊆ ball 0 1 := by
  intro y hy
  apply bump0_support 1 one_pos
  intro h0; apply hy; simp [phi1, h0]

lemma phi1_hasCompactSupport : HasCompactSupport phi1 :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1)
    (phi1_support.trans ball_subset_closedBall)

lemma phi1_integral : ∫ y, phi1 y = 1 := by
  simp only [phi1]
  rw [integral_const_mul, inv_mul_cancel₀ (bump0_integral_pos 1 one_pos).ne']

/-- The rescaled mollifier `φ_ρ(y) = ρ⁻³ φ₁(y/ρ)`. -/
noncomputable def phiR (ρ : ℝ) : R3 → ℝ := fun y => (ρ ^ 3)⁻¹ * phi1 (ρ⁻¹ • y)

lemma phiR_contDiff (ρ : ℝ) {n : ℕ∞} : ContDiff ℝ n (phiR ρ) :=
  contDiff_const.mul (phi1_contDiff.comp (contDiff_const_smul _))

lemma phiR_support (ρ : ℝ) (hρ : 0 < ρ) : Function.support (phiR ρ) ⊆ ball 0 ρ := by
  intro y hy
  have h1 : ρ⁻¹ • y ∈ ball (0 : R3) 1 := by
    apply phi1_support; intro h0; apply hy; simp [phiR, h0]
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)] at h1
  rw [mem_ball, dist_zero_right]
  rwa [inv_mul_lt_iff₀ hρ, mul_one] at h1

lemma phiR_hasCompactSupport (ρ : ℝ) (hρ : 0 < ρ) : HasCompactSupport (phiR ρ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ρ)
    ((phiR_support ρ hρ).trans ball_subset_closedBall)

lemma phiR_integral (ρ : ℝ) (hρ : 0 < ρ) : ∫ y, phiR ρ y = 1 := by
  simp only [phiR]
  rw [integral_const_mul, Measure.integral_comp_smul volume, finrank_euclideanSpace_fin, phi1_integral]
  simp only [smul_eq_mul, mul_one, inv_pow, inv_inv]
  rw [abs_of_pos (by positivity), inv_mul_cancel₀ (by positivity)]

lemma fderiv_phiR_norm (ρ : ℝ) (hρ : 0 < ρ) (y : R3) :
    ‖fderiv ℝ (phiR ρ) y‖ = (ρ ^ 3)⁻¹ * ρ⁻¹ * ‖fderiv ℝ phi1 (ρ⁻¹ • y)‖ := by
  have hd : HasFDerivAt (fun y : R3 => phi1 (ρ⁻¹ • y))
      ((fderiv ℝ phi1 (ρ⁻¹ • y)).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ R3)) y :=
    ((phi1_contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_smul ρ⁻¹)
  have h := (hd.const_mul ((ρ ^ 3)⁻¹)).fderiv
  rw [show phiR ρ = fun y => (ρ ^ 3)⁻¹ * phi1 (ρ⁻¹ • y) from rfl, h,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul, norm_smul,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  ring

lemma integral_fderiv_phiR (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ y, ‖fderiv ℝ (phiR ρ) y‖ = ρ⁻¹ * ∫ y, ‖fderiv ℝ phi1 y‖ := by
  simp only [fderiv_phiR_norm ρ hρ]
  rw [integral_const_mul,
    Measure.integral_comp_smul volume (fun y => ‖fderiv ℝ phi1 y‖) ρ⁻¹, finrank_euclideanSpace_fin]
  simp only [smul_eq_mul, inv_pow, inv_inv]
  rw [abs_of_pos (by positivity)]
  field_simp

theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ) (U : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen U → InnerProductSpace.HarmonicOnNhd f U →
      ∀ (z : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ U →
      ∀ K : ℝ, (∀ w ∈ Metric.closedBall z r, ‖f w‖ ≤ K) →
        ‖fderiv ℝ f z‖ ≤ C / r * K := by
  set I := ∫ y, ‖fderiv ℝ phi1 y‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  refine ⟨2 * I + 1, by positivity, fun f U hU hf z r hr hzr K hK => ?_⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK z (mem_closedBall_self hr.le))
  set ρ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  -- cut-off and convolution
  set g := Set.indicator (closedBall z r) f with hg
  have hfc : ContinuousOn f (closedBall z r) := fun y hy =>
    ((hf y (hzr hy)).1.continuousAt).continuousWithinAt
  have hgli : LocallyIntegrable g volume :=
    ((integrable_indicator_iff measurableSet_closedBall).mpr
      (hfc.integrableOn_compact (isCompact_closedBall z r))).locallyIntegrable
  have hφint : Integrable (phiR ρ) :=
    (phiR_contDiff ρ (n := 0)).continuous.integrable_of_hasCompactSupport
      (phiR_hasCompactSupport ρ hρ)
  have hrad : ∀ y y' : R3, ‖y‖ = ‖y'‖ → phiR ρ y = phiR ρ y' := by
    intro y y' h
    simp only [phiR, phi1, bump0, norm_smul, h]
  have hev : f =ᶠ[nhds z] (convolution (phiR ρ) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    filter_upwards [ball_mem_nhds z hρ] with w hw
    have hwU : closedBall w ρ ⊆ U := by
      refine (closedBall_subset_closedBall' ?_).trans hzr
      rw [mem_ball] at hw; linarith
    rw [harmonic_radial_mollifier_R3 f U hU hf (phiR ρ) hrad hφint (phiR_integral ρ hρ) ρ hρ
      (phiR_support ρ hρ) w hwU, convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.lsmul_apply]
    by_cases hy : phiR ρ y = 0
    · simp [hy]
    · have hyb : y ∈ ball (0 : R3) ρ := phiR_support ρ hρ hy
      have hmem : w - y ∈ closedBall z r := by
        rw [mem_closedBall, dist_eq_norm]
        rw [mem_ball, dist_zero_right] at hyb
        rw [mem_ball, dist_eq_norm] at hw
        calc ‖w - y - z‖ = ‖(w - z) - y‖ := by congr 1; abel
          _ ≤ ‖w - z‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ r := by linarith
      simp [hg, Set.indicator_of_mem hmem]
  have hderiv := (phiR_hasCompactSupport ρ hρ).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (phiR_contDiff ρ) hgli z
  rw [hev.fderiv_eq, hderiv.fderiv, convolution_def]
  -- estimate the integral
  have hDint : Integrable fun t => ‖fderiv ℝ (phiR ρ) t‖ :=
    (((phiR_contDiff ρ (n := 1)).continuous_fderiv one_ne_zero).norm).integrable_of_hasCompactSupport
      ((phiR_hasCompactSupport ρ hρ).fderiv (𝕜 := ℝ)).norm
  have hbd : ∀ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompL R3
      (fderiv ℝ (phiR ρ) t) (g (z - t))‖ ≤ K * ‖fderiv ℝ (phiR ρ) t‖ := by
    intro t
    have hgt : ‖g (z - t)‖ ≤ K := by
      by_cases hm : z - t ∈ closedBall z r
      · simp only [hg, Set.indicator_of_mem hm]; exact hK _ hm
      · simp only [hg, Set.indicator_of_notMem hm, norm_zero]; exact hK0
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, norm_smul]
    calc ‖fderiv ℝ (phiR ρ) t v‖ * ‖g (z - t)‖ ≤ (‖fderiv ℝ (phiR ρ) t‖ * ‖v‖) * K :=
          mul_le_mul (ContinuousLinearMap.le_opNorm _ _) hgt (norm_nonneg _) (by positivity)
      _ = K * ‖fderiv ℝ (phiR ρ) t‖ * ‖v‖ := by ring
  calc _ ≤ ∫ t, K * ‖fderiv ℝ (phiR ρ) t‖ :=
        norm_integral_le_of_norm_le (hDint.const_mul K) (Filter.Eventually.of_forall hbd)
    _ = K * (ρ⁻¹ * I) := by rw [integral_const_mul, integral_fderiv_phiR ρ hρ]
    _ ≤ (2 * I + 1) / r * K := by
        rw [hρdef]
        have : K * ((r / 2)⁻¹ * I) = 2 * I / r * K := by field_simp
        rw [this]
        gcongr
        linarith
