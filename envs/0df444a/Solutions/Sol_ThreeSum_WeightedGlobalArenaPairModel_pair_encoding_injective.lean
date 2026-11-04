-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairModel.pair_encoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:47:03.877093+00:00
-- url     : https://prove2.me/submissions/291f8ad9-0637-46c4-a30e-3d275f57f55d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_left_occurrence
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_right_occurrence
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_block_injective


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
theorem _root_.solution {i : ℕ}
    (hi : i<(Host (r := r) maps τ cap localQ I).front.count) :
    Function.Injective (fun x : Pair (Host (r := r) maps τ cap localQ I) i =>
      ((x.val.1.1,x.val.2.1),edge hi x)) := by
  intro x y he
  have heB := congrArg (fun z : (ℕ×ℕ)×(Fin r→ActualEdge m) => z.1.1) he
  have heC := congrArg (fun z : (ℕ×ℕ)×(Fin r→ActualEdge m) => z.1.2) he
  have heE := congrArg (fun z : (ℕ×ℕ)×(Fin r→ActualEdge m) => z.2) he
  have hl : leftIndex x=leftIndex y := by
    apply WeightedGlobalCanonicalSourceBank.block_injective false maps cap
    funext t
    apply Prod.ext
    · exact (congrFun (left_occurrence hi x) t).trans (congrFun (left_occurrence hi y) t).symm
    · apply Subtype.ext
      exact congrArg left (congrFun heE t)
  have hr : rightIndex x=rightIndex y := by
    apply WeightedGlobalCanonicalSourceBank.block_injective true maps cap
    funext t
    apply Prod.ext
    · exact (congrFun (right_occurrence hi x) t).trans (congrFun (right_occurrence hi y) t).symm
    · apply Subtype.ext
      exact congrArg right (congrFun heE t)
  apply Subtype.ext
  exact Prod.ext (Prod.ext heB (congrArg Fin.val hl)) (Prod.ext heC (congrArg Fin.val hr))
end ThreeSum.WeightedGlobalArenaPairModel
