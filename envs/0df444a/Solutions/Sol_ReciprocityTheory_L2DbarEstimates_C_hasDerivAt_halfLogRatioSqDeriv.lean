-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_halfLogRatioSqDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:24.772094+00:00
-- url     : https://prove2.me/submissions/9b69bf1e-ec2a-4943-a128-b86f9ac3b329

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
theorem _root_.solution {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε s) s := by
  have h1 := (hasDerivAt_cutL h).div ((hasDerivAt_id s).add_const ε) h.ne'
  show HasDerivAt (fun s => cutL ε s / (s + ε)) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqSecondDeriv
  simp only [id]
  field_simp
end ReciprocityTheory.L2DbarEstimates.C
