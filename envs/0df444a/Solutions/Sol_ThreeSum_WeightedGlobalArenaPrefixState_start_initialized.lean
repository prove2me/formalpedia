-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixState.start_initialized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:08:54.658588+00:00
-- url     : https://prove2.me/submissions/0d124479-8d71-480f-9a6b-233a95b0492e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_start
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaPrefixState
theorem _root_.solution (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (values : List ℤ) (initial μ : ℕ→ℤ)
    (H : LightWeightedGlobalPrefixInit.Initialized (config p 1 I A 0) (addr I.free I.capacity 3) values initial μ) :
    Memory I A L R O 0 (WeightedGlobalArenaSelectedBudgets.initial (p := p) A) (fun _ _ => 0) initial μ := by
  apply start I A L R O initial μ ?_ H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2.1
  intro x hx
  exact H.2.2.2.2.2 x (Or.inl (by unfold addr;omega))
    (Or.inl (by change x<addr I.free I.capacity 4;unfold addr;omega))
    (Or.inl (by change x<addr I.free I.capacity 7;unfold addr;omega))
end ThreeSum.WeightedGlobalArenaPrefixState
