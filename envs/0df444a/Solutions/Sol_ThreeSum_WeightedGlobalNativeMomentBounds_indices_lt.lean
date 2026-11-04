-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeMomentBounds.indices_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:07:04.531389+00:00
-- url     : https://prove2.me/submissions/4a8ea015-1827-43d7-a343-cc0ef2f891a0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators
namespace ThreeSum.WeightedGlobalNativeMomentBounds
theorem _root_.solution {N : ℕ} {S : WeightedSourceCountExecutionFactory.Setup N} {i : ℕ}
    (p : Pair S i) : p.val.1.1<S.left.NL ∧ p.val.2.1<S.right.NL := by
  classical
  have hp := p.property
  change p.val∈((leftSet S i)×ˢ(rightSet S i)).filter
    (fun x => TernaryConvolution.Adds (leftWord S x.1) (rightWord S x.2) (S.front.Q i)) at hp
  have ht := mem_product.mp (mem_filter.mp hp).1
  have hl := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (mem_filter.mp ht.1).1
  have hr := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (mem_filter.mp ht.2).1
  exact ⟨hl.1,hr.1⟩
end ThreeSum.WeightedGlobalNativeMomentBounds
