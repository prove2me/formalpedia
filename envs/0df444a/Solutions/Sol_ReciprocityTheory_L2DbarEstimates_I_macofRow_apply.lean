-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.macofRow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:03.409985+00:00
-- url     : https://prove2.me/submissions/b0a2b5b0-a8b1-40ad-b864-7af9698d9ef9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (u : Fin n → ℂ) :
    macofRow M i u = (M.updateRow i u).det := rfl
end ReciprocityTheory.L2DbarEstimates.I
