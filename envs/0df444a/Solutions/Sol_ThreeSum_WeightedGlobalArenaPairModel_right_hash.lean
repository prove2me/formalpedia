-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairModel.right_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:47:10.052931+00:00
-- url     : https://prove2.me/submissions/a2d7b239-43c1-4a99-a104-6986eb73f00d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_right_occurrence
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
    WeightedGlobalCanonicalSourceBank.nativeRow true maps cap (rightIndex x) t=
      rightHash (maps (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1)
        (edge hi x t) := by
  have ho := congrFun (right_occurrence hi x) t
  change TernaryCoverHashes.linearHash
    (TernaryCoverHashes.rightVector (fieldWord p (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).2.val))
    (maps (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).1)=_
  rw [ho]
  rfl
end ThreeSum.WeightedGlobalArenaPairModel
