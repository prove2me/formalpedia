-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopABI.cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:11:22.31962+00:00
-- url     : https://prove2.me/submissions/a0604753-4a90-4cd0-98f1-0d0db10124a4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000
namespace ThreeSum.WeightedGlobalColoredLoopABI
theorem _root_.solution (m F p alpha2 alphaRank localQ R a b scale : ℕ) :
    ((loopArgs m F p alpha2 alphaRank localQ R a b scale).map Expr.cost).sum=23 := by rfl
end ThreeSum.WeightedGlobalColoredLoopABI
