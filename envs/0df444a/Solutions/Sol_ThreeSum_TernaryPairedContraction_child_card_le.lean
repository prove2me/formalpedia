-- Prove2me | solution 1 for ThreeSum.TernaryPairedContraction.child_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:41.797435+00:00
-- url     : https://prove2.me/submissions/61158ad3-414d-4ab5-b71a-89eed9fa4fb0

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverOutputCap_outputFiber_card_le
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedContraction
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThreeSum.TernaryPairedContraction
theorem _root_.solution (L m F : ℕ) (α π : DigitType) :
    Fintype.card (Child L m F α π) ≤ F*(vertices L π).card*(2^(π 1)*3^(π 2))^m := by
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma]
  have hh : (∑ q : vertices L π, Fintype.card (Fin m → outputFiber α π q.val)) ≤
      (vertices L π).card*(2^(π 1)*3^(π 2))^m := by
    calc
      _ ≤ ∑ _q : vertices L π, (2^(π 1)*3^(π 2))^m := by
        apply sum_le_sum
        intro q hq
        rw [Fintype.card_fun,Fintype.card_fin]
        exact Nat.pow_le_pow_left (outputFiber_card_le α π q.val (mem_filter.mp q.property).2) m
      _ = _ := by simp
  exact (Nat.mul_le_mul_left F hh).trans_eq (by ring)
end ThreeSum.TernaryPairedContraction
