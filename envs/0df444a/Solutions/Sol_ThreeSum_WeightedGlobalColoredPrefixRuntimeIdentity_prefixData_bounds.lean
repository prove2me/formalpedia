-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.prefixData_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:15:38.040597+00:00
-- url     : https://prove2.me/submissions/d0d1a156-f3b0-4fc6-b2c5-26ceea344355

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLoop
open LightWeightedGlobalSeedScoreFactory WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
open WeightedGlobalActualSeedRuntime
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
theorem _root_.solution {p m F K N : ℕ} [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (S : Setup p m F K N E) (j seed : ℕ) :
    (prefixData S j seed).bB=S.featureBound ∧
    (prefixData S j seed).bC=S.featureBound ∧
    (prefixData S j seed).bO=S.featureBound :=by
  cases j <;> exact ⟨rfl,rfl,rfl⟩
end ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
