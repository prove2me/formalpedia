-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColoredSolver.arenaArgs_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:55:25.749745+00:00
-- url     : https://prove2.me/submissions/9b55066f-75ac-4d08-9e5b-2b5335aeced7

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
theorem _root_.solution (p R F : ℕ) : (arenaArgs p R F).length=23 := rfl
end ThreeSum.LightWeightedGlobalColoredSolver
