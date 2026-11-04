-- Prove2me | solution 1 for ThreeSum.BandRawA.sorted_equation_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:20.843641+00:00
-- url     : https://prove2.me/submissions/bcee39ae-d6dd-4432-adbb-f47964b0ab1a

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandCandidateRows_records_length
import Theorems.Thm_ThreeSum_BandCandidateRows_slot_lt
import Theorems.Thm_ThreeSum_BandPartition_covers
import Theorems.Thm_ThreeSum_BandPartition_index_bounds
import Theorems.Thm_ThreeSum_BandPartition_index_lt_size
import Theorems.Thm_ThreeSum_BandRawA_count_zero
import Theorems.Thm_ThreeSum_BandRawA_firstRows_zero
import Definitions.Def_WeightedCache3SUM_Alias_147f5e85bb4446a6
import Theorems.Thm_ThreeSum_BandRawA_values_getD
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_zero
import Theorems.Thm_ThreeSum_Bands_exact_equation_relevant
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Theorems.Thm_ThreeSum_BlockIndex_coordEquiv_val
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_card
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_subset
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_union
import Theorems.Thm_ThreeSum_BlockIndex_index_unindex
import Theorems.Thm_ThreeSum_BlockIndex_mem_indexSet
import Theorems.Thm_ThreeSum_BlockIndex_unindex_index
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
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
import Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_covers
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BandRawA.count_zero
attribute [local simp] ThreeSum.BandRawA.firstRows_zero
attribute [local simp] ThreeSum.BandWeightedScore.partialScore_zero
attribute [local simp] ThreeSum.BlockCoefficientRows.mapRow_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockIndex.coordEquiv_val
attribute [local simp] ThreeSum.BlockIndex.indexSet_card
attribute [local simp] ThreeSum.BlockIndex.indexSet_subset
attribute [local simp] ThreeSum.BlockIndex.indexSet_union
attribute [local simp] ThreeSum.BlockIndex.index_unindex
attribute [local simp] ThreeSum.BlockIndex.mem_indexSet
attribute [local simp] ThreeSum.BlockIndex.unindex_index
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero



set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {A B C : List ℤ} {g : ℕ} {a b c : ℤ}
    (hg : 0 < g) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·))
    (hsC : C.Pairwise (· < ·)) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c := by
  obtain ⟨ia,hia,hA⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨ib,hib,hB⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨ic,hic,hC⟩ := List.mem_iff_getElem.mp hc
  have hAget : A.getD ia 0=a := (List.getD_eq_getElem A 0 hia).trans hA
  have hBget : B.getD ib 0=b := (List.getD_eq_getElem B 0 hib).trans hB
  have hCget : C.getD ic 0=c := (List.getD_eq_getElem C 0 hic).trans hC
  let FA := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let FB := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let FC := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  let band : Triple FA FB FC :=
    (⟨ia/g,index_lt_size hia⟩,⟨ib/g,index_lt_size hib⟩,⟨ic/g,index_lt_size hic⟩)
  have hAband : FA.lo band.1 ≤ a ∧ a ≤ FA.hi band.1 := by
    simpa only [FA,band,Family.lo,Family.hi,hAget] using covers (fun i => A.getD i 0) A.length g hg
      (LightSortedBands.getD_strict hsA) hia
  have hBband : FB.lo band.2.1 ≤ b ∧ b ≤ FB.hi band.2.1 := by
    simpa only [FB,band,Family.lo,Family.hi,hBget] using covers (fun i => B.getD i 0) B.length g hg
      (LightSortedBands.getD_strict hsB) hib
  have hCband : FC.lo band.2.2 ≤ c ∧ c ≤ FC.hi band.2.2 := by
    simpa only [FC,band,Family.lo,Family.hi,hCget] using covers (fun i => C.getD i 0) C.length g hg
      (LightSortedBands.getD_strict hsC) hic
  have hrel : relevant FA FB FC band := Bands.exact_equation_relevant hAband hBband hCband heq
  have hap : start g band.1.val ≤ ia ∧ ia < stop A.length g band.1.val := index_bounds hg hia
  have hbp : start g band.2.1.val ≤ ib ∧ ib < stop B.length g band.2.1.val := index_bounds hg hib
  have hcp : start g band.2.2.val ≤ ic ∧ ic < stop C.length g band.2.2.val := index_bounds hg hic
  obtain ⟨k,hk,hlabel,hproduct⟩ := relevant_product_complete band hrel hap hbp hcp
  have hs : slot FA FB FC (owner FA FB FC band) < (records FA FB FC).length := by
    rw [records_length]
    exact slot_lt FA FB FC _
  have hall : (k,ib,ic) ∈ allProducts A.length B.length C.length g (records FA FB FC) :=
    mem_biUnion.mpr ⟨slot FA FB FC (owner FA FB FC band),mem_range.mpr hs,hproduct⟩
  refine ⟨(k,ib,ic),hall,?_,hBget,hCget⟩
  change valueAt A.length g (records FA FB FC) (fun i => A.getD i 0) k=a
  rw [valueAt,values_getD _ hk,hlabel]
  exact hAget
end ThreeSum.BandRawA
