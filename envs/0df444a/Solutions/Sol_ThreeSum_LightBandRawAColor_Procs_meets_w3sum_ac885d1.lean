-- Prove2me | solution 1 for ThreeSum.LightBandRawAColor.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:46:47.918877+00:00
-- url     : https://prove2.me/submissions/18ab0df0-183b-4e4d-8ff0-2f637ac441e8

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_WeightedCache3SUM_Alias_162bee3568c215d0
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandCandidateRows_records_length
import Theorems.Thm_ThreeSum_BandPartition_size_mono
import Theorems.Thm_ThreeSum_BandRawA_count_mono
import Theorems.Thm_ThreeSum_BandRawA_count_zero
import Theorems.Thm_ThreeSum_BandRawA_firstRows_zero
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_zero
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
import Theorems.Thm_ThreeSum_ColorClassLists_length_classList_le
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
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
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_f945b0797ad8c830
import Theorems.Thm_ThreeSum_LightBandCandidates_time_bound
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_a6ca635f54b46105
import Definitions.Def_WeightedCache3SUM_Alias_2186ec26acc49293
import Definitions.Def_WeightedCache3SUM_Alias_1109447aa6c56181
import Theorems.Thm_ThreeSum_LightBandRawACatalog_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
import Definitions.Def_WeightedCache3SUM_Alias_0eeb60918c21319a
import Theorems.Thm_ThreeSum_LightBandRawA_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_e24e346b903ae22f
import Theorems.Thm_ThreeSum_LightColorBands_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Theorems.Thm_ThreeSum_LightColorClasses_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
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
attribute [local simp] ThreeSum.ColorClassLists.value_fin
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
attribute [local simp] ThreeSum.LightClassFilter.items_zero
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
open ThreeSum ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBandRawAColor
namespace Procs
theorem _root_.solution {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2 ^ W)
    (hg : 0 < g) (hsrc : src + n ≤ colors) (hcolors : colors + n ≤ dst0) (h0 : dst0 + n + 1 ≤ dst1)
    (h1 : dst1 + n + 1 ≤ dst2) (h2 : dst2 + n + 1 ≤ av) (hav : av + n ≤ ae) (hae : ae + 2 + 2 * n ≤ bv)
    (hbv : bv + n ≤ be) (hbe : be + 2 + 2 * n ≤ cv) (hcv : cv + n ≤ ce) (hce : ce + 2 + 2 * n ≤ work)
    (htable : work + ColorBandBounds.count n g ≤ rec) (hrec : rec + 4 * ColorBandBounds.count n g ≤ vals)
    (hspace : space work vals W n g ≤ lim.space) (hword : (word W n g U : ℤ) ≤ lim.word)
    (hd : d + depth W n g ≤ lim.depth) (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [src, n, W, p.1.1.val, p.1.2.val, (p.2 (false, false)).val, (p.2 (false, true)).val, (p.2 (true, false)).val,
        (p.2 (true, true)).val, colors, dst0, dst1, dst2, g, av, ae, bv, be, cv, ce, work, rec, vals]
      μ (time W n g)
      (fun r ν =>
        Output ν av ae bv be cv ce work rec vals g hg (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) :=
  by
  have hcSpace :=
    (Nat.le_max_left (LightColorBands.space work W n g) (LightBandRawA.space vals (ColorBandBounds.count n g) g)).trans
      hspace
  have hrSpace :=
    (Nat.le_max_right (LightColorBands.space work W n g) (LightBandRawA.space vals (ColorBandBounds.count n g) g)).trans
      hspace
  have hcWord : (LightColorBands.word W n g U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightColorBands.word W n g U ≤ word W n g U by unfold word; omega)).trans hword
  have hcDepth : d + 1 + LightColorBands.depth W n g ≤ lim.depth := by unfold depth at hd; omega
  have hrDepth : d + 1 + 3 < lim.depth := by unfold depth at hd; omega
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  have len2 := length_classList_le p x 2 (-1)
  apply Meets.of_body R.main
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.color.meets (d := d + 1) p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce hcSpace hcWord hcDepth
              hread hbound)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.color.meets (d := d + 1) p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce hcSpace hcWord hcDepth
            hread hbound)
          ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro colorResult ν₁ ⟨hout, hkeepColor⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  obtain ⟨A, hsA, B, hsB, C, hsC, hcolorResult, hrepA, hrepB, hrepC, htables⟩ := hout
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  have hnA : A.length ≤ n := hrepA.2.1.trans len0
  have hnB : B.length ≤ n := hrepB.2.1.trans len1
  have hnC : C.length ≤ n := hrepC.2.1.trans len2
  have ha : aFamily.size ≤ size n g := size_mono hnA
  have hb : bFamily.size ≤ size n g := size_mono hnB
  have hc : cFamily.size ≤ size n g := size_mono hnC
  have hcount : LightBandEnumeration.count aFamily.size bFamily.size cFamily.size ≤ ColorBandBounds.count n g :=
    by
    have hh := LightBandEnumeration.count_mono ha hb hc
    have heq : LightBandEnumeration.count (size n g) (size n g) (size n g) = ColorBandBounds.count n g := by
      unfold LightBandEnumeration.count ColorBandBounds.count; ring
    rwa [heq] at hh
  have hcatSpace : LightBandRawACatalog.space vals aFamily.size bFamily.size cFamily.size g ≤ lim.space :=
    by
    have hm := Nat.mul_le_mul_left g hcount
    unfold LightBandRawACatalog.space LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
      LightBandRawA.capacity at hrSpace ⊢
    omega
  have hcatWord : (LightBandRawACatalog.word A.length aFamily.size bFamily.size cFamily.size g : ℤ) ≤ lim.word :=
    by
    have hh := LightBandEnumeration.count_mono ha hb hc
    apply
      (Int.ofNat_le.mpr
            (show LightBandRawACatalog.word A.length aFamily.size bFamily.size cFamily.size g ≤ word W n g U
              by
              unfold word LightBandRawACatalog.word LightBandCandidates.word LightBandRawA.word
              omega)).trans
        hword
  have hcatTime : LightBandRawACatalog.time aFamily.size bFamily.size cFamily.size g ≤ catalogTime n g :=
    by
    apply (LightBandRawACatalog.time_bound _ _ _ _).trans
    unfold catalogTime
    exact Nat.mul_le_mul_right (g + 1) (Nat.mul_le_mul_left 3000 (by omega))
  have hsource : ∀ j < A.length, ν₁ (av + j) = A.getD j 0 :=
    by
    intro j hj
    exact hrepA.1.getD hj 0
  have hcat :=
    R.catalog.meets (d := d + 1) (tables := work) (rec := rec) (src := av) (headerA := ae) (headerB := be) (headerC :=
      ce) (vals := vals) aFamily bFamily cFamily rfl hw hrDepth hg (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hcatSpace hcatWord hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2 htables hsource
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
    | refine _root_.Light.Ends.callToThen ((hcat.mono_time hcatTime) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hcat.mono_time hcatTime) ?_ ?_ ?_ ?_
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
      (rintro result ν₂ ⟨hresult, hrecords, hstored, hkeepCatalog⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine
    ⟨⟨A, hsA, B, hsB, C, hsC, hresult, hrepA.keep hkeepCatalog (by omega) (by omega),
        hrepB.keep hkeepCatalog (by omega) (by omega), hrepC.keep hkeepCatalog (by omega) (by omega),
        tables_keep (A := aFamily) (B := bFamily) (C := cFamily) htables hkeepCatalog (by omega), hrecords, ?_⟩,
      ?_⟩
  · simpa only [sortedRecords, records_length] using hstored
  · intro a ha'
    change ν₂ a = μ a
    exact (hkeepCatalog a (by omega)).trans (hkeepColor a ha')
end Procs
end ThreeSum.LightBandRawAColor
