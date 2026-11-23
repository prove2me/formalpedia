-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_cutL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:52.843091+00:00
-- url     : https://prove2.me/submissions/bd24263e-bec2-4919-ba7e-3a6cb4005c73

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA

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
theorem _root_.solution {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutL ε) (s + ε)⁻¹ s := by
  have h1 := (((hasDerivAt_id s).add_const ε).log h.ne').sub_const (Real.log ε)
  show HasDerivAt (fun s => Real.log (s + ε) - Real.log ε) _ s
  simpa [one_div] using h1
end ReciprocityTheory.L2DbarEstimates.C
