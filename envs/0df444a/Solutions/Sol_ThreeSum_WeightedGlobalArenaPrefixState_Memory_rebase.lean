-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixState.Memory.rebase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:50:31.073907+00:00
-- url     : https://prove2.me/submissions/421b16f4-552a-48d8-8194-22de7340c32b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
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
namespace Memory
theorem _root_.solution {I : Input} {A : Inputs} {L R O : ℕ→Fin (A.J+2)→ℤ}
    {j : ℕ} {s : State (p := p) A} {catalog : ℕ→ℕ→ℕ} {initial initial' μ : ℕ→ℤ}
    (H : Memory I A L R O j s catalog initial μ) (hk : Kept initial' initial I.free) :
    Memory I A L R O j s catalog initial' μ :=
  {H with immutable:=fun x hx => (H.immutable x hx).trans (hk x hx)}
end Memory
end ThreeSum.WeightedGlobalArenaPrefixState
