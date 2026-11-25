-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:26.320368+00:00
-- url     : https://prove2.me/submissions/ba66ca9c-eba4-43e0-825d-227152de6276

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson

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
theorem _root_.solution {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : 0 ≤ poissonKernel 0 w z := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  refine div_nonneg ?_ (sq_nonneg _)
  simp only [sub_zero]
  rw [hz]
  nlinarith [norm_nonneg w]
end ReciprocityTheory.AnForm.A
