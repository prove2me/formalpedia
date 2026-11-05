-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.indices_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:20:44.953624+00:00
-- url     : https://prove2.me/submissions/fc19449f-56af-4513-b468-57e2aff927e9

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
