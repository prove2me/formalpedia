-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_hasDerivAt_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:57.260319+00:00
-- url     : https://prove2.me/submissions/5603b824-4477-45d1-83da-cb6cd8af6ed7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (χ : ℝ → ℝ) (hχs : ContDiff ℝ ∞ χ) (ε t : ℝ) :
    HasDerivAt (fun t => χ (t / ε ^ 2)) (deriv χ (t / ε ^ 2) * (1 / ε ^ 2)) t := by
  have h1 : HasDerivAt χ (deriv χ (t / ε ^ 2)) (t / ε ^ 2) :=
    ((hχs.differentiable (by simp)) _).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => t / ε ^ 2) (1 / ε ^ 2) t := (hasDerivAt_id t).div_const _
  exact h1.comp t h2
end ReciprocityTheory.L2DbarEstimates.I
