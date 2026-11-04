-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColoredSolver.budgetLibrary_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:44:07.834132+00:00
-- url     : https://prove2.me/submissions/c01e362f-a243-4ae4-af42-4e3e510b0d72

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
theorem _root_.solution (radix D E K bDigit a b scaleBase : ℕ) :
    (budgetLibrary radix D E K bDigit a b scaleBase).length=55 := rfl
end ThreeSum.LightWeightedGlobalColoredSolver
