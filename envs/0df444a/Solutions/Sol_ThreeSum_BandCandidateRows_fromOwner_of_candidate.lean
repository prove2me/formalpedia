-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.fromOwner_of_candidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:39.905315+00:00
-- url     : https://prove2.me/submissions/256fd7d2-c95b-4554-8dc3-6732302a86dd

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_ThreeSum_BandCandidateRows_lookup_result
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
theorem _root_.solution (A B C : Family) (o : Owner A B C) (t : Triple A B C)
    (hc : candidate A B C o=some t) : fromOwner A B C o=fromTriple t := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · simp only [candidate] at hc
    cases he : A.lookup (C.lo k-B.hi j) with
    | none => simp [he] at hc
    | some a =>
      have ht : (a,j,k)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result A _ a he
      change LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j)=a.val+1 at hr
      simp [fromOwner,bc,make,hr,fromTriple]
  · simp only [candidate] at hc
    cases he : C.lookup (A.lo i+B.lo j) with
    | none => simp [he] at hc
    | some c =>
      have ht : (i,j,c)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result C _ c he
      change LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j)=c.val+1 at hr
      simp [fromOwner,ab,make,hr,fromTriple]
  · simp only [candidate] at hc
    cases he : B.lookup (C.lo k-A.lo i) with
    | none => simp [he] at hc
    | some b =>
      have ht : (i,b,k)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result B _ b he
      change LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)=b.val+1 at hr
      simp [fromOwner,ac,make,hr,fromTriple]
end ThreeSum.BandCandidateRows
