-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llLog_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:06:03.920801+00:00
-- url     : https://prove2.me/submissions/a9002b8e-c0cd-4be0-bf54-c149fa9084a8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llShift_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llShift_pos

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
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (llLog c) :=
  (llShift_contDiff c).log fun t => (llShift_pos hc t).ne'
end ReciprocityTheory.L2DbarEstimates.I
