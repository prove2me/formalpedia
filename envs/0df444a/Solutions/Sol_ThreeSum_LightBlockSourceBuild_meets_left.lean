-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBuild.meets_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:50.145736+00:00
-- url     : https://prove2.me/submissions/d563c2d4-5851-4175-a3de-909edd6fe7a2

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_endpointLeft_abs_le
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_left_value
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
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
import Theorems.Thm_ThreeSum_BlockIndexedQuery_prefixIndices_card
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
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
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
attribute [local simp] ThreeSum.BlockIndexedQuery.prefixIndices_card
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
attribute [local simp] ThreeSum.BlockSourceEncoding.modulus_cast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.SubsetTransport.reindex_map



set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceBuild
theorem _root_.solution {β : Type*} [DecidableEq β] {pMain : ℕ}
    (S : LightSourceBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags n p hist dst codes work U : ℕ}
    (o : Occurrences h J) (B : Finset β) (b : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 0 < p)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+modulus h J ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceBuild.space work p U 0 (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceBuild.word p (modulus h J) U 0 (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < n, μ (raw+i) = endpointLeft o (sets i))
    (hflagRead : ∀ i < n, μ (flags+i) = (if LeftAllowed o (sets i) then 1 else 0 : ℕ)) :
    Meets lim P pMain d [src,N,raw,flags,n,p,modulus h J,hist,dst,codes,work,0]
      μ (LightSourceBuild.time N n p (modulus h J) U 0 (endpointBound h J))
      (fun _ ν => (∀ i < n, ν (dst+i) = (leftWeights o (p : ℤ) B b (sets i) : ℤ)) ∧
        Kept μ ν hist) := by
  have run := S.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw)
    (flags := flags) (n := n) (p := p) (m := modulus h J) (hist := hist) (dst := dst)
    (codes := codes) (work := work) (U := U) (D := 0) (E := endpointBound h J) (shift := 0)
    (fun i => endpointLeft o (sets i)) (fun i => if LeftAllowed o (sets i) then 1 else 0)
    hw hd hp (modulus_pos h J) hsrc hraw hflags hhist hdst hcodes hspace (by simp)
    hword hvalues hrawRead (fun i _ => endpointLeft_abs_le o (sets i)) hflagRead
    (fun i _ => by split <;> omega)
  refine run.mono le_rfl ?_
  rintro r ν ⟨out,_,kept⟩
  refine ⟨?_,kept⟩
  intro i hi
  rw [out i hi,left_value o p B b sets (fun j => μ (src+j)) e hinput i]
end ThreeSum.LightBlockSourceBuild
