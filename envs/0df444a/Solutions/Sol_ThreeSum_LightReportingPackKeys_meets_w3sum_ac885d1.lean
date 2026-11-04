-- Prove2me | solution 1 for ThreeSum.LightReportingPackKeys.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:12:53.31338+00:00
-- url     : https://prove2.me/submissions/82fea0b6-98ff-4060-a4b9-3772cc05c0d3

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
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
import Theorems.Thm_ThreeSum_BlockMaskLayout_packedMasks_length
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_all
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_zero
import Theorems.Thm_ThreeSum_BlockMaskLayout_rawMasks_length
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
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightArray_source_read
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_all
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_zero
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_lt
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_pairKey_lt
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
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
attribute [local simp] ThreeSum.BlockMaskLayout.packedMasks_length
attribute [local simp] ThreeSum.BlockMaskLayout.prefixMask_all
attribute [local simp] ThreeSum.BlockMaskLayout.prefixMask_zero
attribute [local simp] ThreeSum.BlockMaskLayout.rawMasks_length
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
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.ExplicitLayers.leaves_length
attribute [local simp] ThreeSum.ExplicitLayers.missing_length
attribute [local simp] ThreeSum.ExplicitLayers.valueSum_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.MaskUnion.scanSet_all
attribute [local simp] ThreeSum.MaskUnion.scanSet_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.QueryCoordinates.mem_positions
attribute [local simp] ThreeSum.QueryCoordinates.missingSets_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_toFinset
attribute [local simp] ThreeSum.QueryCoordinates.positions_zero
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_sum
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_zero
attribute [local simp] ThreeSum.QueryCoordinates.setLayer_length
attribute [local simp] ThreeSum.QueryCoordinates.total_weights
attribute [local simp] ThreeSum.ReportingHostPairSegments.leftMasks_length
attribute [local simp] ThreeSum.ReportingHostPairSegments.rightMasks_length
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_card
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_empty
attribute [local simp] ThreeSum.ReportingHostSuffix.mem_lowerSet
attribute [local simp] ThreeSum.ReportingHostSuffix.shiftEmbedding_val
attribute [local simp] ThreeSum.SignedLeaf.mem_explicitMissing
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
open ThreeSum ThreeSum.LightReportingPackKeys
open Light LightArray ReportingHostPackedCatalog
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightReportingPackKeys
theorem _root_.solution {p inL inR n radix dst : ℕ} {μ : ℕ → ℤ} (hp : P[p]? = some body) (left right : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hleft : inL + n ≤ dst) (hright : inR + n ≤ dst) (hdst : dst + n ≤ lim.space)
    (hword : (word radix n : ℤ) ≤ lim.word) (hreadL : ∀ i < n, μ (inL + i) = (left i : ℤ))
    (hreadR : ∀ i < n, μ (inR + i) = (right i : ℤ)) (hboundL : ∀ i < n, left i < radix)
    (hboundR : ∀ i < n, right i < radix) :
    Meets lim P p d [inL, inR, n, radix, dst] μ (time n)
      (fun _ μ' => Seg μ' dst (codes (fun i => pairKey radix (left i) (right i)) n) ∧ SameOutside μ μ' dst n) :=
  by
  have hnWord : ((n + 1 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : n + 1 ≤ word radix n)).trans hword
  have hsepL : SourceSafe inL dst n := Or.inr (Or.inl hleft)
  have hsepR : SourceSafe inR dst n := Or.inr (Or.inl hright)
  refine
    .of_body hp
      (Ends.pass (fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ)) (fun i hi => ?_)
        ⟨?_, by
          ( try refine _root_.Light.SameOn.cell ?_
            intro x_p2m_16705842381348184560 hx_p2m_16705842381348184560
            first
            | ((  (repeat
                      ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_169112293001390194);
                        (try have := h_p2m_169112293001390194 x_p2m_16705842381348184560 (by omega));
                        revert h_p2m_169112293001390194))
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at hx_p2m_16705842381348184560;
                ( (repeat
                      ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3506940567485745573);
                        (try have := h_p2m_3506940567485745573 x_p2m_16705842381348184560 (by omega));
                        revert h_p2m_3506940567485745573))
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( (repeat
                      ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_6517767086085340728);
                        (try have := h_p2m_6517767086085340728 x_p2m_16705842381348184560 (by omega));
                        revert h_p2m_6517767086085340728))
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                            its condition K x does not follow from the hypotheses."))⟩
        hw hdst rfl rfl (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time] <;> first
              | omega
              | (ring_nf; omega))))
  · have hrL :=
      source_read (μ := μ) (f := fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ)) hsepL hi
    have hrR :=
      source_read (μ := μ) (f := fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ)) hsepR hi
    have hb := pairKey_lt (hboundL i hi) (hboundR i hi)
    have hf := packed_lt (key := fun j => pairKey radix (left j) (right j)) hi hb
    simp only [packed, pairKey, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hrL hrR
    have hmN : radix * right i ≤ word radix n := by unfold pairKey at hb; unfold word; nlinarith
    have hkN : pairKey radix (left i) (right i) ≤ word radix n := by unfold word; nlinarith
    have hpN : pairKey radix (left i) (right i) * (n + 1) ≤ word radix n :=
      by
      simp only [packed] at hf
      unfold word
      omega
    have hfN : packed (fun j => pairKey radix (left j) (right j)) n i ≤ word radix n :=
      by
      unfold word
      omega
    have hmZ : (radix : ℤ) * (right i : ℤ) ≤ lim.word :=
      (by exact_mod_cast hmN : (radix : ℤ) * (right i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hkZ : (left i : ℤ) + (radix : ℤ) * (right i : ℤ) ≤ lim.word :=
      (by exact_mod_cast hkN : (left i : ℤ) + (radix : ℤ) * (right i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hpZ : ((left i : ℤ) + (radix : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) ≤ lim.word :=
      (by exact_mod_cast hpN : ((left i : ℤ) + (radix : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) ≤ (word radix n : ℤ)).trans
        hword
    have hfZ : ((left i : ℤ) + (radix : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) + (i : ℤ) ≤ lim.word :=
      (by exact_mod_cast hfN :
            ((left i : ℤ) + (radix : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) + (i : ℤ) ≤ (word radix n : ℤ)).trans
        hword
    have hm0 : 0 ≤ (radix : ℤ) * (right i : ℤ) := by positivity
    have hp0 : 0 ≤ ((left i : ℤ) + (radix : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) := by positivity
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrL, hrR, hreadL i hi, hreadR i hi, packed,
          pairKey] <;> omega)
  · intro i hi
    have hi' : i < n := by simpa only [codes, List.length_ofFn] using hi
    simpa only [codes, List.getElem_ofFn] using
      (wrote_done (μ := μ) (dst := dst) (f := fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ))
        hi')
end ThreeSum.LightReportingPackKeys
