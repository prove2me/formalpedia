-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPhaseFrames.template
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:09:44.115197+00:00
-- url     : https://prove2.me/submissions/916d31e8-1fa4-4f1e-85b1-e50ca101dbf5

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseFrames
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseFrames
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open WeightedGlobalArenaControllerPlan WeightedGlobalArenaScoreScan
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSeedData WeightedGlobalArenaPrefixInputs WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPhase
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaPhaseFrames
theorem _root_.solution {I : Input} {μ ω : ℕ→ℤ} {xs : List ℤ}
    (hframe : ∀x,Stable I x→ω x=μ x) (hlen : xs.length≤I.capacity)
    (hseg : Seg μ (addr I.free I.capacity 0) xs) :
    Seg ω (addr I.free I.capacity 0) xs := by
  intro i hi
  have hx : addr I.free I.capacity 0+i<addr I.free I.capacity 1 := by
    unfold addr
    omega
  rw [hframe _ (Or.inl hx)]
  exact hseg i hi
end ThreeSum.WeightedGlobalArenaPhaseFrames
