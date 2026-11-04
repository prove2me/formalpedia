-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColoredSolver.prepArena_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:47:36.077671+00:00
-- url     : https://prove2.me/submissions/281f9556-e6e1-4765-a5cb-225631d2e692

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
theorem _root_.solution (radix D E : ℕ) : (prepArena radix D E).length=53 := rfl
end ThreeSum.LightWeightedGlobalColoredSolver
