-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairModel.left_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:47:01.440992+00:00
-- url     : https://prove2.me/submissions/4c3dbd1f-c35e-4187-bf84-6b686e00e98d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_left_occurrence
import Theorems.Thm_Light_Ends_block


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairModel
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalArenaSourceModel TernaryCoverLocal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input)
variable {maps τ cap localQ I}
namespace ThreeSum.WeightedGlobalArenaPairModel
theorem _root_.solution {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) (t : Fin r) :
    WeightedGlobalCanonicalSourceBank.nativeRow false maps cap (leftIndex x) t=
      leftHash (maps (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1)
        (edge hi x t) := by
  have ho := congrFun (left_occurrence hi x) t
  change TernaryCoverHashes.linearHash
    (TernaryCoverHashes.leftVector (fieldWord p (WeightedGlobalCanonicalSourceBank.block false maps cap (leftIndex x) t).2.val))
    (maps (WeightedGlobalCanonicalSourceBank.block false maps cap (leftIndex x) t).1)=_
  rw [ho]
  rfl
end ThreeSum.WeightedGlobalArenaPairModel
