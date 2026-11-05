-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs.reads
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:44:41.967898+00:00
-- url     : https://prove2.me/submissions/fb5312b3-274a-4d65-a329-d12620453fbe

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedDataReads
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixInputs
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_cell_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_reads
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSeedDataReads_reads
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixInputs
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation
open TernaryOriginalRowMenu WeightedGlobalNativeCompleteFrontend
open TernaryExtensionEncoding
open LightWeightedGlobalSeedScoreFactory
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
private theorem cell_lt {base count width i k stop : ℕ}
    (hend : base+count*width≤stop) (hi : i<count) (hk : k<width) :
    base+i*width+k<stop := by nlinarith
end ThreeSum.WeightedGlobalArenaPrefixInputs
end
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation
open TernaryOriginalRowMenu WeightedGlobalNativeCompleteFrontend
open TernaryExtensionEncoding
open LightWeightedGlobalSeedScoreFactory
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
theorem _root_.solution (I : Input) (A : Inputs) (j featureBound tagBound positionCap seedCount ordinal : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (H : WeightedGlobalArenaPrefixState.Memory I A (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) j s catalog initial μ)
    (hi : ordinal<seedCount) :
    WeightedGlobalArenaSeedPrimitiveGuards.Reads I A ordinal
      (data I A j featureBound ordinal ℓ (seeds ordinal) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) μ positionCap := by
  apply WeightedGlobalArenaSeedDataReads.reads I A j featureBound ordinal positionCap ℓ (seeds ordinal)
    s.row _ _ _ s.rows catalog μ h.BEnd h.CEnd h.OEnd ?_ h.positionEnd h.feature
    (fun i hi t => h.BBound i hi t.val t.isLt)
    (fun i hi t => h.CBound i hi t.val t.isLt)
    (fun i hi t => h.OBound i hi t.val t.isLt)
    ?_ ?_ ?_ ?_ H.B H.Cvalues H.Ovalues H.represents H.bounded H.read ?_ h.positionBound
  · have hh:=Nat.mul_le_mul_right (A.J+2) (show ordinal+1≤seedCount by omega)
    nlinarith [h.menuEnd]
  · intro i hi k hk
    exact (H.immutable _ (cell_lt h.BEnd hi hk)).trans (h.BRead i hi k hk)
  · intro i hi k hk
    exact (H.immutable _ (cell_lt h.CEnd hi hk)).trans (h.CRead i hi k hk)
  · intro i hi k hk
    exact (H.immutable _ (cell_lt h.OEnd hi hk)).trans (h.ORead i hi k hk)
  · intro k hk
    exact (H.immutable _ (cell_lt h.menuEnd hi hk)).trans (h.menuRead ordinal hi k hk)
  · intro i hi
    have hp:=h.positionEnd
    exact (H.immutable _ (by omega)).trans (h.positionRead i hi)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
