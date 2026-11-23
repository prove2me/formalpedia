-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_cutP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:11.024486+00:00
-- url     : https://prove2.me/submissions/31ef74ec-ed23-4f30-b1f6-5bfe950cd766

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_cutL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutP ε) (halfLogRatioSqDeriv ε s) s := by
  have h1 := ((hasDerivAt_cutL h).pow 2).div_const 2
  show HasDerivAt (fun s => cutL ε s ^ 2 / 2) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqDeriv
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates.C
