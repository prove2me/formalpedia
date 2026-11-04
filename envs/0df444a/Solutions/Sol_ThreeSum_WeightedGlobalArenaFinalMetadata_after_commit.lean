-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFinalMetadata.after_commit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:11:13.3842+00:00
-- url     : https://prove2.me/submissions/697e1c10-01f1-4f00-937f-96ebca7a9311

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixCommit_outside
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



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
theorem _root_.solution {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {A : Inputs}
    {rows newSpan : ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (H : LightWeightedGlobalPrefixFinish.Committed (config p r I A 0) rows newSpan μ ν)
    (hO : I.requesterCount≤I.capacity) (hspan : rows*A.J≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    Metadata (r := r) maps τ I ν := by
  have high (x : ℕ) (hx : addr I.free I.capacity 8≤x) : ν x=μ x := by
    apply WeightedGlobalArenaPrefixCommit.outside H x
    · change x<addr I.free I.capacity 4 ∨ addr I.free I.capacity 6+I.requesterCount≤x
      right
      have hh := before (free := I.free) (i := 6) (j := 8) (by decide) hO
      omega
    · change x<addr I.free I.capacity 7 ∨ addr I.free I.capacity 7+rows*A.J≤x
      right
      have hh := before (free := I.free) (i := 7) (j := 8) (by decide) hspan
      omega
  have hbase : addr I.free I.capacity 8≤I.prefixFree := by rw [hprefix]; unfold addr; omega
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [high _ (by omega)]
    exact M.codes i hi
  · intro i hi
    rw [high _ (hbase.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))]
    exact M.powers i hi
  · intro i hi
    rw [high _ (by unfold addr; omega)]
    exact M.wanted i hi
end ThreeSum.WeightedGlobalArenaFinalMetadata
