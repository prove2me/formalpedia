-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames.seed_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:01:41.842934+00:00
-- url     : https://prove2.me/submissions/ceb8d384-c904-47d0-9f3c-2a5375caffcb

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseFrames
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames
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
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames
theorem _root_.solution {I : Input} {μ ω : ℕ→ℤ} {xs : List ℤ} {offset : ℕ}
    (hframe : ∀x,Stable I x→ω x=μ x) (hlen : offset+xs.length≤I.capacity)
    (hseg : Seg μ (addr I.free I.capacity 2+offset) xs) :
    Seg ω (addr I.free I.capacity 2+offset) xs := by
  intro i hi
  have hx : addr I.free I.capacity 2≤addr I.free I.capacity 2+offset+i ∧
      addr I.free I.capacity 2+offset+i<addr I.free I.capacity 3 := by
    unfold addr
    omega
  rw [hframe _ (Or.inr hx)]
  exact hseg i hi
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames
