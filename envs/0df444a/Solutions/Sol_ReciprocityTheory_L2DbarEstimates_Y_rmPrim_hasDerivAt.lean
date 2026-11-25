-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmPrim_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:00.402165+00:00
-- url     : https://prove2.me/submissions/c5e12ef1-948c-4034-9a9d-c07fafe2e6cc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmStep_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (t : ℝ) : HasDerivAt rmPrim (rmStep t) t :=
  (rmStep_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
end ReciprocityTheory.L2DbarEstimates.Y
