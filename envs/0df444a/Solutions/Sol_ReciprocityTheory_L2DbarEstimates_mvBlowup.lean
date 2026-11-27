-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.mvBlowup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:36.218608+00:00
-- url     : https://prove2.me/submissions/1292199a-59eb-473b-bbf5-fc5c0093f2e6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mvDiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Metric Filter Topology
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) : MVBlowupStatement n :=
  fun hn => C.mvDiv n hn
end ReciprocityTheory.L2DbarEstimates
