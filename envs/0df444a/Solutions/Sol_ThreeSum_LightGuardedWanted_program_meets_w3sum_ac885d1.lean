-- Prove2me | solution 1 for ThreeSum.LightGuardedWanted.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:26:16.899631+00:00
-- url     : https://prove2.me/submissions/63f5e4bc-b155-47fe-bde6-6793f5fc6f48

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Theorems.Thm_ThreeSum_LightGuardedWanted_selected_eq
import Theorems.Thm_ThreeSum_LightGuardedWanted_left_bound
import Theorems.Thm_ThreeSum_LightGuardedWanted_right_bound
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
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
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f4d14ad9782635c8
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7dc97c785b0d6c4c
import Theorems.Thm_ThreeSum_LightCoverKeyData_free_le_keyEnd
import Theorems.Thm_ThreeSum_LightCoverKeyData_global_length
import Theorems.Thm_ThreeSum_LightCoverKeyData_program_meets
import Theorems.Thm_ThreeSum_LightCoverKeys_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2311045817689c86
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_8622643736b2cec4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_d3fb44062fe6c749
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_0a77a2090c5d3d77
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Theorems.Thm_ThreeSum_LightLocalParameters_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_b5aa5d62f09c4909
import Theorems.Thm_ThreeSum_LightRawAKeys_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_RawAKeyLists_keys_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
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
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {lim : Limits}
namespace ThreeSum.LightGuardedWanted
theorem _root_.solution {μ : ℕ → ℤ} {a free P M h J U d : ℕ} [NeZero M] (xs : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hP : 0 < P) (ha : a + xs.length ≤ free) (hspace : space free P M h J U xs ≤ lim.space)
    (hword : (word P M h J U xs.length : ℤ) ≤ lim.word)
    (hd : d + 512 * h + J + Nat.clog 2 M + 3 * xs.length + 12 ≤ lim.depth) (hread : Seg μ a xs)
    (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim program 98 d [h, J, a, xs.length, P, M, free] μ (time P M h J U xs)
      (fun r ν =>
        r = (wantedFree free h J xs.length : ℤ) ∧
          LightWantedSetup.Output ν (wantedFree free h J xs.length) M (left P xs) (right h J) (3 * xs.length)
              (totalKeys h J) (RawAKeyLists.selected M P xs h J) ∧
            M * (ν (wantedFree free h J xs.length)).toNat ≤ 3 * xs.length * totalKeys h J ∧
              LightCoverKeyData.Stored ν free h J ∧
                Seg ν (LightCoverKeyData.keyEnd free h J) (RawAKeyLists.keys P xs) ∧ Kept μ ν free) :=
  by
  let keyHead := LightCoverKeys.keyHeader free h J
  let rawBase := LightCoverKeyData.keyEnd free h J
  let out := wantedFree free h J xs.length
  have hkeyEnd : rawBase = keyHead + 1 + totalKeys h J := rfl
  have hout : out = rawBase + 3 * xs.length := rfl
  have hcoverSpace : LightCoverKeys.space free h J ≤ lim.space := (le_max_left _ _).trans hspace
  have hliftSpace : LightRawAKeys.space rawBase xs.length U ≤ lim.space :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hspace)
  have hwantedSpace :
    LightBalancedWanted.space out M (left P xs) (right h J) (3 * xs.length) (totalKeys h J) (keyBound P h J) ≤
      lim.space :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hspace)
  have hcoverWord : (LightCoverKeys.word h J : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hliftWord : (LightRawAKeys.word P U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (le_max_right _ _))).trans hword
  have hwantedWord : (LightBalancedWanted.word M (3 * xs.length) (totalKeys h J) (keyBound P h J) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hword
  have hrawSpace : rawBase + 3 * xs.length + Nat.log 2 (U + 1) + 2 ≤ lim.space := hliftSpace
  have hfree : free ≤ rawBase := LightCoverKeyData.free_le_keyEnd free h J
  have htripleWord : (3 * (xs.length : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3 * xs.length ≤ lim.space by omega) : (3 * (xs.length : ℤ)) ≤ lim.space).trans hw
  apply Meets.of_body (p := 98) (by rfl : program[98]? = some (body 67 68 97))
  unfold body time
  have hc :=
    (((LightCoverKeyData.program_meets (d := d + 1) (μ := μ) (h := h) (J := J) (free := free) hw (by omega) hcoverSpace
                  hcoverWord).append
              (LightRawAKeys.program.map (ReportingHostRelocation.relocate 68))).append
          (LightBalancedWanted.program.map (ReportingHostRelocation.relocate 72))).append
      [body 67 68 97]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro header μ₁ ⟨hheader, H, hkeepC⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcount := H.count
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (totalKeys h J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hheader, hcount, totalKeys]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hheader, hcount, totalKeys] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hheader, hcount, totalKeys] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (keyHead + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hheader, keyHead]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hheader, keyHead] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hheader, keyHead] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (rawBase : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hkeyEnd]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hkeyEnd] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkeyEnd] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (3 * xs.length : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (out : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hout] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hx₁ : Seg μ₁ a xs := by
    apply hread.congr
    intro i hi
    exact hkeepC _ (by omega)
  have hl :=
    ((ReportingHostRelocation.meets
              (LightRawAKeys.program_meets (d := d + 1) (μ := μ₁) (src := a) (free := rawBase) (p := P) (U := U) xs hw
                hP (by omega) hliftSpace hliftWord (by omega) hx₁ hvalues)
              LightCoverKeys.program).append
          (LightBalancedWanted.program.map (ReportingHostRelocation.relocate 72))).append
      [body 67 68 97]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro rawHead μ₂ ⟨hrawHead, hraw, hkeepL⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hleft (i : ℕ) (hi : i < 3 * xs.length) : μ₂ (rawBase + i) = left P xs i :=
    by
    have hi' : i < (RawAKeyLists.keys P xs).length := by rwa [RawAKeyLists.keys_length]
    rw [left, List.getD_eq_getElem _ _ hi']
    exact hraw i hi'
  have hright (j : ℕ) (hj : j < totalKeys h J) : μ₂ (keyHead + 1 + j) = right h J j :=
    by
    have hj' : j < (globalKeys h J).length := by rwa [LightCoverKeyData.global_length]
    rw [hkeepL _ (by omega), right, List.getD_eq_getElem _ _ hj']
    exact H.keys j hj'
  have hb :=
    (ReportingHostRelocation.meets
          (LightBalancedWanted.program_meets (d := d + 1) (μ := μ₂) (a := rawBase) (b := keyHead + 1) (NL :=
            3 * xs.length) (NR := totalKeys h J) (M := M) (free := out) (U := keyBound P h J) (left P xs) (right h J) hw
            (by omega) (by omega) hwantedSpace hwantedWord (by omega) hleft hright (left_bound hP xs)
            (right_bound h J P))
          liftProgram).append
      [body 67 68 97]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 =>
      (rintro result ν ⟨hresult, houtput, hbound, hkeepB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hretain : Kept μ₁ ν rawBase := by
    intro i hi
    exact (hkeepB _ (by omega)).trans (hkeepL i hi)
  refine ⟨hresult, ?_, hbound, H.of_kept hretain, ?_, ?_⟩
  · simpa only [selected_eq] using houtput
  · apply hraw.congr
    intro i hi
    rw [RawAKeyLists.keys_length] at hi
    exact hkeepB _ (by omega)
  · intro i hi
    exact (hretain i (by omega)).trans (hkeepC i hi)
end ThreeSum.LightGuardedWanted
