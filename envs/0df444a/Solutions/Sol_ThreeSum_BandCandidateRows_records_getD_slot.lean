-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.records_getD_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:57.579186+00:00
-- url     : https://prove2.me/submissions/a373ddf7-f3e4-49de-ab43-94f1dabb8d58

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_ThreeSum_BandCandidateRows_rect_length
import Theorems.Thm_ThreeSum_BandCandidateRows_index_lt
import Theorems.Thm_ThreeSum_BandCandidateRows_rect_getD
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution (A B C : Family) (o : Owner A B C) :
    (records A B C).getD (slot A B C o) default=fromOwner A B C o := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · simp only [records,slot,fromOwner]
    rw [List.getD_append _ _ _ _ (by rw [rect_length]; exact index_lt j.isLt k.isLt)]
    exact rect_getD _ j.isLt k.isLt
  · simp only [records,slot,fromOwner]
    rw [List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff : B.size*C.size+i.val*B.size+j.val-B.size*C.size=i.val*B.size+j.val := by omega
    rw [hoff,List.getD_append _ _ _ _ (by rw [rect_length]; exact index_lt i.isLt j.isLt)]
    exact rect_getD _ i.isLt j.isLt
  · simp only [records,slot,fromOwner]
    rw [List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff : B.size*C.size+A.size*B.size+i.val*C.size+k.val-B.size*C.size=
        A.size*B.size+i.val*C.size+k.val := by omega
    rw [hoff,List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff' : A.size*B.size+i.val*C.size+k.val-A.size*B.size=i.val*C.size+k.val := by omega
    rw [hoff']
    exact rect_getD _ i.isLt k.isLt
end ThreeSum.BandCandidateRows
