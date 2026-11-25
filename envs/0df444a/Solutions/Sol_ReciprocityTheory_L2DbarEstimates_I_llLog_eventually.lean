-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llLog_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:17.774359+00:00
-- url     : https://prove2.me/submissions/20926ac9-1f71-4ca5-9402-2389a46823ae

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llShift_eq

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    llLog c =ᶠ[𝓝 t] fun s => Real.log (s + c) := by
  filter_upwards [lt_mem_nhds ht] with s hs
  simp [llLog, llShift_eq hc hs.le]
end ReciprocityTheory.L2DbarEstimates.I
