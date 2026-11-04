-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPhaseFrames.input_lt_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:03:57.79974+00:00
-- url     : https://prove2.me/submissions/7dc6ba12-9ed0-40f9-8d98-1eb1da55eb57

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseFrames
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


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
theorem _root_.solution {n M r L : ℕ} (hn : 1<n) (hsize : n^2≤M^r) (hM : M≤4^L) :
    n<2^(2*(r*L)) := by
  calc
    n<n^2 := by nlinarith
    _≤M^r := hsize
    _≤(4^L)^r := Nat.pow_le_pow_left hM r
    _=2^(2*(r*L)) := by
      rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul]
      congr 1
      ring
end ThreeSum.WeightedGlobalArenaPhaseFrames
