-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.dualK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:30.203893+00:00
-- url     : https://prove2.me/submissions/eae73ecc-49e0-4639-a774-69ee5f6346ff

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualSig_eq

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
universe u
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {c t : ℝ} (h : 7 / 8 ≤ c - t) :
    dualK c t = -Real.log ((c - t) + Real.log (c - t)) := by
  unfold dualK
  rw [dualSig_eq h]
end ReciprocityTheory.L2DbarEstimates.I
