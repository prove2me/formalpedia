-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFinalMetadata.after_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:58:05.883141+00:00
-- url     : https://prove2.me/submissions/693b60c3-f05d-43d2-ab02-b996c6537cc0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalMetadata
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory WeightedGlobalArenaPostMemory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaFinalMetadata
theorem _root_.solution {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {len : ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (H : SameOutside μ ν (addr I.free I.capacity 8) len) (hlen : len≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    Metadata (r := r) maps τ I ν := by
  have high (x : ℕ) (hx : addr I.free I.capacity 9≤x) : ν x=μ x := by
    apply H x (Or.inr ?_)
    unfold addr at *
    omega
  have hb : addr I.free I.capacity 9≤I.prefixFree := by rw [hprefix];unfold addr;omega
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [high _ (by omega)]
    exact M.codes i hi
  · intro i hi
    rw [high _ (hb.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))]
    exact M.powers i hi
  · intro i hi
    rw [high _ (by unfold addr;omega)]
    exact M.wanted i hi
end ThreeSum.WeightedGlobalArenaFinalMetadata
