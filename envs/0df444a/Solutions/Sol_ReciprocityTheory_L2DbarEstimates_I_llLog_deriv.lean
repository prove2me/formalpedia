-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llLog_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:33.959496+00:00
-- url     : https://prove2.me/submissions/04468ce8-b182-4d9b-a558-187951b6f35c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llLog_eventually

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
    deriv (llLog c) t = (t + c)⁻¹ := by
  rw [(llLog_eventually hc ht).deriv_eq]
  have hpos : t + c ≠ 0 := by linarith
  have := ((hasDerivAt_id t).add_const c).log hpos
  simpa using this.deriv
end ReciprocityTheory.L2DbarEstimates.I
