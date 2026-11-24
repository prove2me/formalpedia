-- Prove2me | solution 1 for RoughSurfaceScattering.vCorr_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:09:35.035933+00:00
-- url     : https://prove2.me/submissions/a1d7a9c4-dfb1-484e-933d-0fe4404e8235

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_frontier_hausdorff_finite
import Theorems.Thm_RoughSurfaceScattering_outwardNormal_continuousOn

open MeasureTheory Metric
open RoughSurfaceScattering

lemma phi0_contDiffOn (z : R2) :
    ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 1 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 1 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 1 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 1
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 1
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

lemma dipole0_continuousOn (z ν : R2) :
    ContinuousOn (dipoleSource 0 z ν) {x | x ≠ z} := by
  have hfd := (phi0_contDiffOn z).continuousOn_fderiv_of_isOpen isOpen_ne le_rfl
  exact (continuous_id.clm_apply continuous_const).comp_continuousOn hfd
    |>.congr (fun x _ => rfl)

lemma dipole0_formula (z ν x : R2) (hx : x ≠ z) :
    dipoleSource 0 z ν x =
      ((-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (x - z) ν / ‖x - z‖ ^ 2) : ℝ) : ℂ) := by
  have hy : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ‖x - z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hfun : (fun x' : R2 => Phi 0 x' z) =
      fun x' => (((-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2) : ℝ) : ℂ) := by
    funext x'
    simp only [Phi, if_true, one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hsq : HasFDerivAt (fun x' : R2 => ‖x' - z‖ ^ 2)
      (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ R2)) x :=
    ((hasFDerivAt_id x).sub_const z).norm_sq
  have hlog := (hsq.log hn).const_mul (-(1 / (4 * Real.pi)))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hlog
  unfold dipoleSource
  rw [hfun]
  rw [show (fun x' : R2 => (((-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2) : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun x' => (-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2)) from rfl,
    hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, nsmul_eq_mul]
  congr 1
  field_simp
  ring

/-- The kernel `∂Φ₀(x,y)/∂ν(y)` is the Laplace dipole with pole `x`, evaluated at `y`. -/
lemma kernel_eq (x y v : R2) :
    fderiv ℝ (fun y' => Phi 0 x y') y v = dipoleSource 0 x v y := by
  have : (fun y' => Phi 0 x y') = fun y' => Phi 0 y' x := by
    funext y'; simp [Phi, norm_sub_rev]
  rw [this]; rfl

lemma norm_outwardNormal_le (D : Set R2) (y : R2) : ‖outwardNormal D y‖ ≤ 1 := by
  unfold outwardNormal
  split_ifs with h
  · exact h.choose_spec.1.le
  · simp

theorem solution (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (μ : ℝ) (D0 : Set R2)
    (hD0 : IsC2LambdaDomain lam D0) (n0 xj yj : R2) (hxj : xj ∉ frontier D0)
    (hyj : yj ∉ frontier D0) :
    ContinuousOn (vCorr μ D0 n0 xj yj) D0 := by
  set S := frontier D0 with hS
  set ν : Measure R2 := (Measure.hausdorffMeasure 1 : Measure R2).restrict S with hν
  have hSc : IsClosed S := isClosed_frontier
  have hScpt : IsCompact S := isCompact_of_isClosed_isBounded hSc
    (hD0.2.2.1.closure.subset frontier_subset_closure)
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (frontier_hausdorff_finite lam D0 hD0)⟩
  have hN := outwardNormal_continuousOn lam D0 hD0
  -- the density is continuous, hence bounded, on the compact boundary
  set G : R2 → ℂ := fun y => dipoleSource 0 xj n0 y + dipoleSource 0 yj n0 y with hG
  have hGc : ContinuousOn G S :=
    ((dipole0_continuousOn xj n0).mono fun y hy h => hxj (h ▸ hy)).add
      ((dipole0_continuousOn yj n0).mono fun y hy h => hyj (h ▸ hy))
  obtain ⟨MG, hMG⟩ := hScpt.exists_bound_of_continuousOn hGc
  set F : R2 → R2 → ℂ := fun x y =>
    fderiv ℝ (fun y' => Phi 0 x y') y (outwardNormal D0 y) * G y with hF
  have hv : vCorr μ D0 n0 xj yj =
      fun x => ((2 * μ * (1 - μ) / (μ + 1) ^ 2 : ℝ) : ℂ) * ∫ y, F x y ∂ν := by
    funext x; rfl
  rw [hv]
  refine continuousOn_const.mul fun x0 hx0 => ?_
  refine ContinuousAt.continuousWithinAt ?_
  -- distance from `x₀` to the boundary
  have hx0S : x0 ∉ S := by
    rw [hS, hD0.1.frontier_eq]; exact fun h => h.2 hx0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSc.isOpen_compl x0 hx0S
  have hfar : ∀ x ∈ ball x0 (ε / 2), ∀ y ∈ S, ε / 2 ≤ ‖y - x‖ := by
    intro x hx y hy
    have h1 : ε ≤ dist y x0 := by
      by_contra h; push Not at h
      exact hball (by rwa [mem_ball]) hy
    rw [mem_ball] at hx
    have := dist_triangle y x x0
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at this
    rw [dist_eq_norm] at h1 hx
    linarith
  have hFform : ∀ x ∈ ball x0 (ε / 2), ∀ y ∈ S, F x y =
      ((-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (y - x) (outwardNormal D0 y) / ‖y - x‖ ^ 2) : ℝ)
        : ℂ) * G y := by
    intro x hx y hy
    have hyx : y ≠ x := by
      intro h; have := hfar x hx y hy; rw [h, sub_self, norm_zero] at this; linarith
    simp only [hF]
    rw [kernel_eq, dipole0_formula _ _ _ hyx]
  apply continuousAt_of_dominated (bound := fun _ => 1 / (2 * Real.pi) * (2 / ε) * MG)
  · -- measurability
    filter_upwards [ball_mem_nhds x0 (by positivity : 0 < ε / 2)] with x hx
    have hcont : ContinuousOn (F x) S := by
      have hform : ContinuousOn (fun y =>
          ((-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (y - x) (outwardNormal D0 y) /
            ‖y - x‖ ^ 2) : ℝ) : ℂ) * G y) S := by
        refine ContinuousOn.mul ?_ hGc
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        refine continuousOn_const.mul (ContinuousOn.div ?_ (by fun_prop) ?_)
        · exact (continuousOn_id.sub continuousOn_const).inner hN
        · intro y hy
          have := hfar x hx y hy
          exact (pow_pos (by linarith) 2).ne'
      exact hform.congr fun y hy => hFform x hx y hy
    exact hcont.aestronglyMeasurable hSc.measurableSet
  · -- domination
    filter_upwards [ball_mem_nhds x0 (by positivity : 0 < ε / 2)] with x hx
    filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
    rw [hFform x hx y hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd := hfar x hx y hy
    have hdpos : 0 < ‖y - x‖ := by linarith
    have hin : |@inner ℝ R2 _ (y - x) (outwardNormal D0 y)| ≤ ‖y - x‖ := by
      calc _ ≤ ‖y - x‖ * ‖outwardNormal D0 y‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖y - x‖ * 1 := by gcongr; exact norm_outwardNormal_le D0 y
        _ = _ := mul_one _
    have hk : |-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (y - x) (outwardNormal D0 y) /
        ‖y - x‖ ^ 2)| ≤ 1 / (2 * Real.pi) * (2 / ε) := by
      have hpi : 0 < 1 / (2 * Real.pi) := by positivity
      rw [abs_mul, abs_neg, abs_of_pos hpi, abs_div, abs_of_pos (pow_pos hdpos 2)]
      refine mul_le_mul_of_nonneg_left ?_ hpi.le
      have h1 : |@inner ℝ R2 _ (y - x) (outwardNormal D0 y)| / ‖y - x‖ ^ 2 ≤ 1 / ‖y - x‖ := by
        rw [div_le_div_iff₀ (pow_pos hdpos 2) hdpos]; nlinarith [hin]
      have h2 : 1 / ‖y - x‖ ≤ 2 / ε := by
        rw [div_le_div_iff₀ hdpos hε]; linarith
      exact h1.trans h2
    exact mul_le_mul hk (hMG y hy) (norm_nonneg _) (by positivity)
  · exact integrable_const _
  · -- continuity in the parameter
    filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
    have hyx0 : y ≠ x0 := fun h => hx0S (h ▸ hy)
    have hcont : ContinuousAt (fun x =>
        ((-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (y - x) (outwardNormal D0 y) /
          ‖y - x‖ ^ 2) : ℝ) : ℂ) * G y) x0 := by
      refine ContinuousAt.mul ?_ continuousAt_const
      refine Complex.continuous_ofReal.continuousAt.comp ?_
      refine continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
      have : 0 < ‖y - x0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx0)
      positivity
    refine hcont.congr ?_
    filter_upwards [ball_mem_nhds x0 (by positivity : 0 < ε / 2)] with x hx
    exact (hFform x hx y hy).symm
