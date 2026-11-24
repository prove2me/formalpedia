-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonKernel_zero_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:33.582489+00:00
-- url     : https://prove2.me/submissions/0e2ec27e-33bc-4754-99bc-43c19503a858

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Metric Real Filter Topology InnerProductSpace
namespace ReciprocityTheory.AnForm.A
private lemma sub_ne_zero_of_mem_sphere_of_mem_ball {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : z - w ≠ 0 := by
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  intro h
  rw [sub_eq_zero] at h
  rw [h] at hz
  linarith
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 r) := by
  have hfun : poissonKernel 0 w = fun z ↦ (‖z - 0‖ ^ 2 - ‖w - 0‖ ^ 2) / ‖z - 0 - (w - 0)‖ ^ 2 :=
    funext (poissonKernel_def 0 w)
  rw [hfun]
  refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
    (Continuous.continuousOn (by fun_prop)) ?_
  intro z hz
  have h := sub_ne_zero_of_mem_sphere_of_mem_ball hw hz
  simp only [sub_zero]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
end ReciprocityTheory.AnForm.A
