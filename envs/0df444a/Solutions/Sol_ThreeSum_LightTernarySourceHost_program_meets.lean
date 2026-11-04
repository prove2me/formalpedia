-- Prove2me | solution 1 for ThreeSum.LightTernarySourceHost.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:43:38.747552+00:00
-- url     : https://prove2.me/submissions/440d0baa-c429-40e0-9d74-a11866f7dbfb

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Definitions.Def_Submission_ThreeSum_TernarySourceHostRecords
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
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
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_le_offset
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Theorems.Thm_ThreeSum_LightWantedSetup_program_length
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Definitions.Def_WeightedCache3SUM_Alias_f8621e0ea40777d9
import Theorems.Thm_ThreeSum_RadixKeyLists_values_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernarySourceHostRecords_pair_reads
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
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
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHost
open Light RadixKeyLists ThreeSum.LightSubsetAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {lim : Limits}
namespace ThreeSum.LightTernarySourceHost
theorem _root_.solution (xs ys zs : List ℤ) (hxy : ys.length = xs.length) (hxz : zs.length = xs.length)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d src NL M free a bank powers W L keyBase valueBase weightBase
      weightU factor groups U : ℕ}
    (μ : ℕ → ℤ) (input weight : ℕ → ℤ) (codes key group : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < xs.length)
    (hbase0 : base0 + xs.length ≤ dst0) (hnext0 : LightRadixKeys.space dst0 xs.length J ≤ base1)
    (hbase1 : base1 + xs.length ≤ dst1) (hnext1 : LightRadixKeys.space dst1 xs.length J ≤ base2)
    (hbase2 : base2 + xs.length ≤ dst2) (hinitEnd : LightRadixKeys.space dst2 xs.length J ≤ free)
    (hsrc : src + NL ≤ base0) (hweights : weightBase + NL ≤ base0) (hbank : a + bank ≤ base0)
    (hpowerEnd : powers + (W + 1) ≤ base0)
    (hkeyBase : LightWantedSetup.space free M input (dictionary xs p0 J) NL (size xs J) U 0 0 ≤ keyBase)
    (hkeyEnd : keyBase + count xs p0 J M NL input ≤ valueBase) (hvalues : valueBase + groups * bank ≤ lim.space)
    (hb0 : ∀ x ∈ xs, |x| ≤ (U0 : ℤ)) (hb1 : ∀ x ∈ ys, |x| ≤ (U1 : ℤ)) (hb2 : ∀ x ∈ zs, |x| ≤ (U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word) (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word) (hM : 0 < M)
    (hjoinWord : (LightSourceResidues.word M M U 0 : ℤ) ≤ lim.word)
    (hlookupWord : ((bank + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hgroupWord : ((groups * bank + 1 : ℕ) : ℤ) ≤ lim.word) (hgroupSpace : groups * bank + 1 ≤ lim.space)
    (hfactor : (factor : ℤ) ≤ lim.word) (hweighted : (factor : ℤ) * (count xs p0 J M NL input * weightU : ℕ) ≤ lim.word)
    (hhistWord : ((count xs p0 J M NL input + 1 : ℕ) : ℤ) * weightU ≤ lim.word)
    (hinput : ∀ i < NL, μ (src + i) = input i) (hinputBound : ∀ i < NL, |input i| ≤ (U : ℤ))
    (hweightRead : ∀ i < NL, μ (weightBase + i) = weight i) (hweightBound : ∀ i < NL, |weight i| ≤ (weightU : ℤ))
    (hglobal : U0 * (p0 + 1) ^ J ≤ U) (hcodes : ∀ i < bank, μ (a + i) = (codes i : ℤ))
    (hcodeBound : ∀ i < bank, codes i < 2 ^ W) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k)
    (hwordCode : ∀ j < size xs J, dictionary ys p1 J j = (codes (key j) : ℤ)) (hkey : ∀ j < size xs J, key j < bank)
    (hgroupCode : ∀ j < size xs J, dictionary zs p2 J j = (group j : ℤ)) (hgroup : ∀ j < size xs J, group j < groups)
    (hL : L ≤ W) (hn : bank < 2 ^ L) (hd : d + NL + L + J + 8 ≤ lim.depth) :
    Meets lim (program xs ys zs) 34 d
      [base0, dst0, base1, dst1, base2, dst2, J, p0, p1, p2, src, NL, M, free, a, bank, powers, L, keyBase, valueBase,
        weightBase, factor, groups]
      μ (time xs ys zs p0 J M NL U L bank groups input)
      (fun r ν =>
        r = (valueBase : ℤ) ∧
          Kept μ ν base0 ∧
            ∃ ps : List (ℕ × ℕ),
              ps.length = count xs p0 J M NL input ∧
                ps.Nodup ∧
                  (∀ i j, (i, j) ∈ ps ↔ i < NL ∧ j < size xs J ∧ (M : ℤ) ∣ input i - dictionary xs p0 J j) ∧
                    ∀ r < groups * bank,
                      ν (valueBase + r) =
                        (factor : ℤ) *
                          LightTernaryWeightedHistogram.total
                            (fun i => group (ps.getD i (0, 0)).2 * bank + key (ps.getD i (0, 0)).2)
                            (fun i => weight (ps.getD i (0, 0)).1) r (count xs p0 J M NL input)) :=
  by
  let NR := size xs J
  let hits := count xs p0 J M NL input
  let pb := LightWantedSetup.pairBase free NL NR M
  have hfreeKey : free ≤ keyBase :=
    by
    have hp := Nat.le_max_left (LightSourceResidues.space pb M U 0) (pb + 2 * hits)
    unfold LightWantedSetup.space at hkeyBase
    have hpb : free ≤ pb := by
      unfold pb LightWantedSetup.pairBase LightWantedSetup.bucketBase LightWantedSetup.rightCodes
        LightWantedSetup.leftCodes LightSourceBucketSetup.next;
      omega
    have hh := (Nat.le_max_right (LightSourceResidues.space pb M U 0) (pb + 2 * hits)).trans hkeyBase
    omega
  have hkeySpace : keyBase ≤ lim.space := by omega
  have hinitSpace : LightRadixKeys.space dst2 xs.length J ≤ lim.space := by omega
  have h1Space : LightRadixKeys.space dst1 xs.length J ≤ free := by unfold LightRadixKeys.space at hinitEnd; omega
  have h0Space : LightRadixKeys.space dst0 xs.length J ≤ free := by unfold LightRadixKeys.space at h1Space; omega
  have hDict0End : dst0 + LightRadixKeys.offset xs.length J + 1 + NR ≤ free := by
    simpa only [LightRadixKeys.space, NR, size] using h0Space
  have hDict1End : dst1 + LightRadixKeys.offset xs.length J + 1 + NR ≤ free := by
    simpa only [LightRadixKeys.space, NR, size] using h1Space
  have hDict2End : dst2 + LightRadixKeys.offset xs.length J + 1 + NR ≤ free := by
    simpa only [LightRadixKeys.space, NR, size] using hinitEnd
  have hFreeW : (free : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hfreeKey.trans hkeySpace)).trans hw
  have hMW : (M : ℤ) ≤ lim.word := by unfold LightSourceResidues.word at hjoinWord; omega
  have hdct :=
    (LightTernaryParallelDictionaries.program_meets xs ys zs (d := d + 1) μ hw hbase0 hnext0
          (by simpa only [hxy] using hbase1) (by simpa only [hxy] using hnext1) (by simpa only [hxz] using hbase2)
          (by simpa only [hxz] using hinitSpace) hm (by omega) (by omega) hb0 hb1 hb2 hw0 hw1 hw2 (by omega)).append
      ((LightTernaryOriginalJoin.program.map (ReportingHostRelocation.relocate 16)) ++
          (LightTernaryGroupedSources.program.map (ReportingHostRelocation.relocate 28)) ++
        [body])
  have hdct' :
    Meets lim (program xs ys zs) 15 (d + 1) [base0, dst0, base1, dst1, base2, dst2, J, p0, p1, p2] μ
      (LightTernaryParallelDictionaries.time xs ys zs J)
      (fun r ν =>
        r = ((dst2 + LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧
          LightTernaryParallelDictionaries.output ν dst0 xs p0 J ∧
            LightTernaryParallelDictionaries.output ν dst1 ys p1 J ∧
              LightTernaryParallelDictionaries.output ν dst2 zs p2 J ∧ Kept μ ν base0) :=
    by
    simpa only [program, libraries, joined, ReportingHostRelocation.program, LightTernaryParallelDictionaries.program,
      LightTernaryParallelDictionaries.libraries, LightFixedRadixDictionary.program, LightTernaryOriginalJoin.program,
      LightWantedSetup.program_length, LightTernaryGroupedSources.program, List.length_cons, List.length_nil,
      List.length_append, List.length_map, Nat.reduceAdd, List.append_assoc, hxz] using hdct
  have hp0 : (p0 : ℤ) ≤ lim.word := by unfold LightRadixKeys.word LightRadixRows.word at hw0; omega
  have hp1 : (p1 : ℤ) ≤ lim.word := by unfold LightRadixKeys.word LightRadixRows.word at hw1; omega
  have hp2 : (p2 : ℤ) ≤ lim.word := by unfold LightRadixKeys.word LightRadixRows.word at hw2; omega
  have hJ : (J : ℤ) ≤ lim.word := by
    have hh := LightRadixKeys.le_offset xs.length J
    unfold LightRadixKeys.space at hinitSpace; omega
  have hAllBase : dst2 ≤ lim.space := by unfold LightRadixKeys.space at hinitSpace; omega
  have hAllWord : (dst2 : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hAllBase).trans hw
  have hSpaceBases0 : dst0 ≤ dst2 := by unfold LightRadixKeys.space at hnext0 hnext1; omega
  have hSpaceBases1 : dst1 ≤ dst2 := by unfold LightRadixKeys.space at hnext1; omega
  have hbase0W : (base0 : ℤ) ≤ lim.word := by omega
  have hbase1W : (base1 : ℤ) ≤ lim.word := by omega
  have hbase2W : (base2 : ℤ) ≤ lim.word := by omega
  have hdst0W : (dst0 : ℤ) ≤ lim.word := by omega
  have hdst1W : (dst1 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body (by rfl : (program xs ys zs)[34]? = some body)
  unfold body time
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
    | refine _root_.Light.Ends.callToThen (hdct' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hdct' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWantedSetup.time,
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWantedSetup.time,
            LightTernaryGroupedSources.time] <;> omega)
    on_goal -1 =>
      (rintro head μ0 ⟨hhead, hout0, hout1, hout2, hkeep0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hheader : μ0 head.toNat = (NR : ℤ) := by rw [hhead]; simpa only [NR, size, hxz, Int.toNat_natCast] using hout2.1
  have hNR : (NR : ℤ) ≤ lim.word := by unfold NR size; unfold LightRadixKeys.space at hinitSpace; omega
  have hHeaderAddr : dst2 + LightRadixKeys.offset xs.length J < lim.space := by
    unfold LightRadixKeys.space at hinitSpace; omega
  have hheaderDirect : μ0 (dst2 + LightRadixKeys.offset xs.length J) = (NR : ℤ) := by
    simpa only [NR, size, hxz] using hout2.1
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (NR : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hheader, hheaderDirect, hhead, hHeaderAddr,
            LightWantedSetup.time, LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hheader, hheaderDirect, hhead, hHeaderAddr, LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hheader, hheaderDirect, hhead, hHeaderAddr,
            LightWantedSetup.time, LightTernaryGroupedSources.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (LightRadixKeys.offset xs.length J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, LightWantedSetup.time,
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhead, LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, LightWantedSetup.time,
            LightTernaryGroupedSources.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (dst0 + LightRadixKeys.offset xs.length J + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWantedSetup.time,
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWantedSetup.time,
            LightTernaryGroupedSources.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (dst1 + LightRadixKeys.offset xs.length J + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWantedSetup.time,
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWantedSetup.time,
            LightTernaryGroupedSources.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (dst2 + LightRadixKeys.offset xs.length J + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWantedSetup.time,
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWantedSetup.time,
            LightTernaryGroupedSources.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hinput0 (i : ℕ) (hi : i < NL) : μ0 (src + i) = input i := (hkeep0 _ (by omega)).trans (hinput i hi)
  have hdict0 (j : ℕ) (hj : j < NR) : μ0 (dst0 + LightRadixKeys.offset xs.length J + 1 + j) = dictionary xs p0 J j :=
    by
    unfold dictionary
    rw [List.getD_eq_getElem _ _ (by simpa only [values_length, NR, size] using hj)]
    exact hout0.2 j (by simpa only [values_length, NR, size] using hj)
  have hbound (j : ℕ) (hj : j < NR) : |dictionary xs p0 J j| ≤ (U : ℤ) :=
    by
    unfold dictionary
    rw [List.getD_eq_getElem _ _ (by simpa only [values_length, NR, size] using hj)]
    exact
      (values_bounded p0 U0 xs hb0 J _ (List.getElem_mem (by simpa only [values_length, NR, size] using hj))).trans
        (Int.ofNat_le.mpr hglobal)
  have hjBase :=
    ReportingHostRelocation.meets
      (LightWantedSetup.program_meets (d := d + 1) input (dictionary xs p0 J) hw hM (by omega : src + NL ≤ free)
        hDict0End (hkeyBase.trans hkeySpace) hjoinWord (by simp) (by omega) hinput0 hdict0 hinputBound hbound)
      (LightTernaryParallelDictionaries.program xs ys zs)
  have hj := hjBase.append ((LightTernaryGroupedSources.program.map (ReportingHostRelocation.relocate 28)) ++ [body])
  have hj' :
    Meets lim (program xs ys zs) 27 (d + 1) [src, dst0 + LightRadixKeys.offset xs.length J + 1, NL, NR, M, 0, free] μ0
      (LightWantedSetup.time M input (dictionary xs p0 J) NL NR U 0 0)
      (fun r ν =>
        r = (free : ℤ) ∧ LightWantedSetup.Output ν free M input (dictionary xs p0 J) NL NR 0 ∧ Kept μ0 ν free) :=
    by
    simpa only [program, libraries, joined, ReportingHostRelocation.program, LightTernaryParallelDictionaries.program,
      LightTernaryParallelDictionaries.libraries, LightFixedRadixDictionary.program, LightTernaryOriginalJoin.program,
      LightWantedSetup.program_length, LightTernaryGroupedSources.program, List.length_cons, List.length_nil,
      List.length_append, List.length_map, Nat.reduceAdd, List.append_assoc, NR, size, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one] using hj
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
    | refine _root_.Light.Ends.callToThen (hj' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hj' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, NR, LightWantedSetup.time,
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [NR, LightWantedSetup.time, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, NR, LightWantedSetup.time,
            LightTernaryGroupedSources.time] <;> omega)
    on_goal -1 => (rintro res μ1 ⟨hres, houtput, hkeep1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  obtain ⟨hcount, hpairptr, hend, hshift, ps, hlen, hnodup, hmem, hseg⟩ := houtput
  have hcount' : μ1 free = (hits : ℤ) := hcount
  have hpairptr' : μ1 (free + 1) = (pb : ℤ) := hpairptr
  have hpairEnd : pb + 2 * hits ≤ keyBase := (Nat.le_max_right _ _).trans hkeyBase
  have hpbLower : free + 4 ≤ pb :=
    by
    unfold pb LightWantedSetup.pairBase LightWantedSetup.bucketBase LightWantedSetup.rightCodes
      LightWantedSetup.leftCodes LightSourceBucketSetup.next
    omega
  have hcountW : (hits : ℤ) ≤ lim.word := by omega
  have hpbW : (pb : ℤ) ≤ lim.word := by omega
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (hits : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, NR, hres, hcount',
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [NR, hres, hcount', LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, NR, hres, hcount',
            LightTernaryGroupedSources.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (pb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, NR, hres, hpairptr',
            LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [NR, hres, hpairptr', LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, NR, hres, hpairptr',
            LightTernaryGroupedSources.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  let original := fun i => (ps.getD i (0, 0)).1
  let position := fun i => (ps.getD i (0, 0)).2
  have hpos (i : ℕ) (hi : i < hits) : original i < NL ∧ position i < NR :=
    by
    have hip : i < ps.length := by omega
    have hpmem : ps.getD i (0, 0) ∈ ps := by rw [List.getD_eq_getElem _ _ hip]; exact List.getElem_mem hip
    exact ⟨(hmem _ _).mp hpmem |>.1, (hmem _ _).mp hpmem |>.2.1⟩
  have hpairRead (i : ℕ) (hi : i < hits) :
    μ1 (pb + 2 * i) = (original i : ℤ) ∧ μ1 (pb + 2 * i + 1) = (position i : ℤ) :=
    TernarySourceHostRecords.pair_reads ps μ1 pb hseg i (by omega)
  have hwordRead (i : ℕ) (hi : i < hits) :
    μ1 (dst1 + LightRadixKeys.offset xs.length J + 1 + position i) = (codes (key (position i)) : ℤ) :=
    by
    rw [hkeep1 _ (by have hh := (hpos i hi).2; unfold LightRadixKeys.space at h1Space; omega)]
    have hj := (hpos i hi).2
    have hr := hout1.2 (position i) (by simpa only [values_length, hxy, NR, size] using hj)
    rw [← List.getD_eq_getElem _ 0 (by simpa only [values_length, hxy, NR, size] using hj)] at hr
    simpa only [hxy] using hr.trans (hwordCode _ hj)
  have hgroupRead (i : ℕ) (hi : i < hits) :
    μ1 (dst2 + LightRadixKeys.offset xs.length J + 1 + position i) = (group (position i) : ℤ) :=
    by
    rw [hkeep1 _ (by have hh := (hpos i hi).2; unfold LightRadixKeys.space at hinitEnd; omega)]
    have hj := (hpos i hi).2
    have hr := hout2.2 (position i) (by simpa only [values_length, hxz, NR, size] using hj)
    rw [← List.getD_eq_getElem _ 0 (by simpa only [values_length, hxz, NR, size] using hj)] at hr
    simpa only [hxz] using hr.trans (hgroupCode _ hj)
  have hcodeRead (i : ℕ) (hi : i < bank) : μ1 (a + i) = (codes i : ℤ) :=
    (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (hcodes i hi))
  have hpows : Powers μ1 powers W := fun i hi =>
    (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (hpowers i hi))
  have hweightsRead (i : ℕ) (hi : i < hits) : μ1 (weightBase + original i) = weight (original i) :=
    (hkeep1 _ (by have hh := (hpos i hi).1; omega)).trans
      ((hkeep0 _ (by have hh := (hpos i hi).1; omega)).trans (hweightRead _ (hpos i hi).1))
  have hhBase :=
    ReportingHostRelocation.meets
      (LightTernaryGroupedSources.meets (P := LightTernaryGroupedSources.program) (pMain := 0) (pKeys := 1) (pHist := 3)
        (pScale := 5) (pSearch := 2) (pFill := 4) (d := d + 1) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) μ1
        codes position original (fun i => key (position i)) (fun i => group (position i)) (fun i => weight (original i))
        factor hw (by omega) hpairEnd (by unfold LightRadixKeys.space at h1Space; omega) (by omega) (by omega)
        (by unfold LightRadixKeys.space at hinitEnd; omega) hgroupRead (fun i hi => hgroup _ (hpos i hi).2) hgroupWord
        hgroupSpace hkeyEnd hvalues hlookupWord hfactor hweighted hhistWord hcodeRead (fun i hi => (hpairRead i hi).2)
        (fun i hi => (hpos i hi).2) hwordRead (fun i hi => hkey _ (hpos i hi).2) hcodeBound hpows hsorted
        (fun i hi => (hpairRead i hi).1) (fun i hi => (hpos i hi).1) hweightsRead
        (fun i hi => hweightBound _ (hpos i hi).1) hL hn (by omega))
      (joined xs ys zs)
  have hh := hhBase.append [body]
  have hh' :
    Meets lim (program xs ys zs) 28 (d + 1)
      [a, bank, powers, L, pb, hits, dst1 + LightRadixKeys.offset xs.length J + 1, NR, keyBase, valueBase, weightBase,
        NL, factor, dst2 + LightRadixKeys.offset xs.length J + 1, groups]
      μ1 (LightTernaryGroupedSources.time L hits bank groups)
      (fun _ ν =>
        (∀ r < groups * bank,
            ν (valueBase + r) =
              (factor : ℤ) *
                LightTernaryWeightedHistogram.total (fun i => group (position i) * bank + key (position i))
                  (fun i => weight (original i)) r hits) ∧
          ∀ x, (x < keyBase ∨ keyBase + hits ≤ x) → (x < valueBase ∨ valueBase + groups * bank ≤ x) → ν x = μ1 x) :=
    by
    simpa only [program, libraries, joined, ReportingHostRelocation.program, LightTernaryParallelDictionaries.program,
      LightTernaryParallelDictionaries.libraries, LightFixedRadixDictionary.program, LightTernaryOriginalJoin.program,
      LightWantedSetup.program_length, LightTernaryGroupedSources.program, List.length_cons, List.length_nil,
      List.length_append, List.length_map, Nat.reduceAdd, List.append_assoc, Nat.cast_add, Nat.cast_one] using hh
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
    | refine _root_.Light.Ends.callToThen (hh' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, NR, hits, LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [NR, hits, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, NR, hits, LightTernaryGroupedSources.time] <;> omega)
    on_goal -1 => (rintro out ν ⟨hvaluesFinal, hkeepFinal⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (valueBase : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, NR, hits, LightTernaryGroupedSources.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [NR, hits, LightTernaryGroupedSources.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, NR, hits, LightTernaryGroupedSources.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ps, hlen, hnodup, ?_, hvaluesFinal⟩
  · intro x hx
    change ν x = μ x
    rw [hkeepFinal x (Or.inl (by omega)) (Or.inl (by omega)), hkeep1 x (by omega), hkeep0 x hx]
  · intro i j
    simpa only [Int.add_zero] using hmem i j
end ThreeSum.LightTernarySourceHost
