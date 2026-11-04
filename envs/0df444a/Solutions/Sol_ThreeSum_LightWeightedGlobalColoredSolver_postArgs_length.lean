-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColoredSolver.postArgs_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:07:26.537846+00:00
-- url     : https://prove2.me/submissions/75e1309b-385c-4a4e-a5eb-1c14381fd81c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalColoredSolver
open Light
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
namespace ThreeSum.LightWeightedGlobalColoredSolver
theorem _root_.solution : postArgs.length=148 := rfl
end ThreeSum.LightWeightedGlobalColoredSolver
