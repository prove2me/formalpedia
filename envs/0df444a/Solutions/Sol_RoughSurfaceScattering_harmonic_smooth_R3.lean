-- Prove2me | solution 1 for RoughSurfaceScattering.harmonic_smooth_R3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T09:58:47.038496+00:00
-- url     : https://prove2.me/submissions/9a909d36-a80b-41e8-8722-e45aa13a8de9
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

theorem solution (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) :
    ∀ n : ℕ, ContDiffOn ℝ n f U := by
  intro n x hx
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  set ε := δ / 3 with hεdef
  have hε : 0 < ε := by positivity
  have hcl : closedBall x (2 * ε) ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
  -- the normalised radial mollifier
  set c := ∫ y, bump0 ε y with hc
  have hcpos : 0 < c := bump0_integral_pos ε hε
  set φ : R3 → ℝ := fun y => c⁻¹ * bump0 ε y with hφ
  have hφsm : ContDiff ℝ (n : ℕ∞) φ := contDiff_const.mul (bump0_contDiff ε)
  have hφsupp : Function.support φ ⊆ ball 0 ε := by
    intro y hy
    apply bump0_support ε hε
    intro h0; apply hy; simp [hφ, h0]
  have hφcs : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ε)
      (hφsupp.trans ball_subset_closedBall)
  have hφint : Integrable φ := hφsm.continuous.integrable_of_hasCompactSupport hφcs
  have hφ1 : ∫ y, φ y = 1 := by
    rw [hφ, integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
  have hrad : ∀ y y' : R3, ‖y‖ = ‖y'‖ → φ y = φ y' := by
    intro y y' h; simp [hφ, bump0, h]
  -- the cut-off of `f`
  set g := Set.indicator (closedBall x (2 * ε)) f with hg
  have hfc : ContinuousOn f (closedBall x (2 * ε)) := fun y hy =>
    ((hf y (hcl hy)).1.continuousAt).continuousWithinAt
  have hgli : LocallyIntegrable g volume :=
    ((integrable_indicator_iff measurableSet_closedBall).mpr
      (hfc.integrableOn_compact (isCompact_closedBall x _))).locallyIntegrable
  have hconv := hφcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφsm hgli
  -- `f` agrees with the convolution near `x`
  have hev : f =ᶠ[nhds x] (convolution φ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    filter_upwards [ball_mem_nhds x hε] with z hz
    have hzU : closedBall z ε ⊆ U := by
      refine (closedBall_subset_closedBall' ?_).trans hcl
      rw [mem_ball] at hz; linarith
    rw [harmonic_radial_mollifier_R3 f U hU hf φ hrad hφint hφ1 ε hε hφsupp z hzU,
      convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.lsmul_apply]
    by_cases hy : φ y = 0
    · simp [hy]
    · have hyb : y ∈ ball (0 : R3) ε := hφsupp hy
      have hmem : z - y ∈ closedBall x (2 * ε) := by
        rw [mem_closedBall, dist_eq_norm]
        rw [mem_ball, dist_zero_right] at hyb
        rw [mem_ball, dist_eq_norm] at hz
        calc ‖z - y - x‖ = ‖(z - x) - y‖ := by congr 1; abel
          _ ≤ ‖z - x‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ 2 * ε := by linarith
      simp [hg, Set.indicator_of_mem hmem]
  exact (hconv.contDiffAt).congr_of_eventuallyEq hev
