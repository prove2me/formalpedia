-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.extCh_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:52.711868+00:00
-- url     : https://prove2.me/submissions/8a08d583-4a12-41fa-bbe1-fcbd0ecf6b59

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA

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
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : ContDiff ℝ ∞ extCh :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
end ReciprocityTheory.L2DbarEstimates.C
