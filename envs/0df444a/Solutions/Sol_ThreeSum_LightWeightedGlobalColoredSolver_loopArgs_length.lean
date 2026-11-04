-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColoredSolver.loopArgs_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:57:59.54132+00:00
-- url     : https://prove2.me/submissions/5fc5aced-0e04-4668-8a02-90d615157f46

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
theorem _root_.solution (m F p alpha2 alphaRank localQ R a b scaleBase : ℕ) :
    (loopArgs m F p alpha2 alphaRank localQ R a b scaleBase).length=17 := rfl
end ThreeSum.LightWeightedGlobalColoredSolver
