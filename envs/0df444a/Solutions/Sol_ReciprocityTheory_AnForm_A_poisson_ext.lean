-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poisson_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:06.951376+00:00
-- url     : https://prove2.me/submissions/a72b7519-6fb1-4e32-83d3-54f262d8ab47

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_harmonicAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere 0 r)) :
    ∃ Φ : ℂ → ℝ, ContinuousOn Φ (Metric.closedBall 0 r) ∧ (∀ ζ ∈ Metric.sphere 0 r, Φ ζ = g ζ) ∧
      Φ 0 = Real.circleAverage g 0 r ∧
      ∀ a s, 0 < s → Metric.closedBall a s ⊆ Metric.ball 0 r → Real.circleAverage Φ a s = Φ a := by
  refine ⟨fun z ↦ if ‖z‖ < r then poissonInt g r z else g z, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with hlt | heq
    · have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hlt
      have hca : ContinuousAt (poissonInt g r) z := by
        first
        | exact (poissonInt_harmonicAt hr hg hzb).1.continuousAt
        | exact (poissonInt_harmonicAt hr hg hzb).contDiffAt.continuousAt
      have hev : poissonInt g r =ᶠ[𝓝 z] fun z ↦ if ‖z‖ < r then poissonInt g r z else g z := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      first
      | exact (hca.congr hev).continuousWithinAt
      | exact (hca.congr_of_eventuallyEq hev.symm).continuousWithinAt
    · have hzs : z ∈ sphere (0 : ℂ) r := mem_sphere_zero_iff_norm.mpr heq
      have hval : (if ‖z‖ < r then poissonInt g r z else g z) = g z :=
        if_neg (by rw [heq]; exact lt_irrefl r)
      show Filter.Tendsto (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z)
        (𝓝[closedBall 0 r] z) (𝓝 (if ‖z‖ < r then poissonInt g r z else g z))
      rw [hval, ← Metric.ball_union_sphere, nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · refine Filter.Tendsto.congr' ?_ (poissonInt_tendsto hr hg hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      · refine Filter.Tendsto.congr' ?_ (hg z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_neg (by rw [mem_sphere_zero_iff_norm.mp hy]; exact lt_irrefl r)]
  · intro ζ hζ
    exact if_neg (by rw [mem_sphere_zero_iff_norm.mp hζ]; exact lt_irrefl r)
  · show (if ‖(0 : ℂ)‖ < r then poissonInt g r 0 else g 0) = Real.circleAverage g 0 r
    rw [if_pos (by rw [norm_zero]; exact hr)]
    exact poissonInt_zero hr
  · intro a s hs hsub
    have hev : Set.EqOn (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z) (poissonInt g r)
        (sphere a |s|) := by
      intro y hy
      rw [abs_of_pos hs] at hy
      have hyb : y ∈ ball (0 : ℂ) r := hsub (sphere_subset_closedBall hy)
      exact if_pos (mem_ball_zero_iff.mp hyb)
    rw [Real.circleAverage_congr_sphere hev]
    have ha : a ∈ ball (0 : ℂ) r := hsub (mem_closedBall_self hs.le)
    show _ = (if ‖a‖ < r then poissonInt g r a else g a)
    rw [if_pos (mem_ball_zero_iff.mp ha)]
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    intro y hy
    rw [abs_of_pos hs] at hy
    exact poissonInt_harmonicAt hr hg (hsub hy)
end ReciprocityTheory.AnForm.A
