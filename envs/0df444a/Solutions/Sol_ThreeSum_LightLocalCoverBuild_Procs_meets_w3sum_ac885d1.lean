-- Prove2me | solution 1 for ThreeSum.LightLocalCoverBuild.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:36:35.003139+00:00
-- url     : https://prove2.me/submissions/287a4115-24e9-4363-b2be-60d706c9acde

import Definitions.Def_Submission_ThreeSum_LightLocalCoverHost
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightMaskBitTable
import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Theorems.Thm_Light_Meets_of_body
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
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_spec
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length
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
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverBuild
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverBuild
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * h + 7 ≤ lim.depth)
    (hspace :
      LightLocalCoverCandidate.space work (512 * h) (LocalMaskGraph.vertexCount (512 * h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks + LocalMaskGraph.vertexCount (512 * h) h ≤ bitPtr)
    (hbits : bitPtr + LocalMaskGraph.vertexCount (512 * h) h * (512 * h) ≤ maps)
    (hmaps : maps + rows h * (2 * (512 * h)) ≤ raw0) (hraw0 : raw0 + 2 * LocalMaskGraph.vertexCount (512 * h) h ≤ raw1)
    (hraw1 : raw1 + 2 * LocalMaskGraph.vertexCount (512 * h) h ≤ hist0) (hhist0 : hist0 + rows h * localPrime h ≤ hist1)
    (hhist1 : hist1 + rows h * localPrime h ≤ matrixPtr) (hmatrix : matrixPtr + rows h * cols h ≤ work)
    (hschedule : work + LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps + scheduleSize h * (2 * (512 * h)) ≤ lim.space) (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512 * h, h, localPrime h, rows h, LocalMaskGraph.vertexCount (512 * h) h, localBucketCap h, masks, bitPtr, maps,
        raw0, raw1, hist0, hist1, matrixPtr, work, scheduleSize h, scheduleMaps]
      μ (time h)
      (fun r ν =>
        r = (scheduleMaps : ℤ) ∧
          Data ν h maps hist0 hist1 matrixPtr ∧
            ScheduleRows ν h scheduleMaps ∧
              (∀ s : Occurrence h, ν (LightCoverGreedy.out work (rows h) (cols h) + s.val) = (candidateAt h s : ℤ)) ∧
                Kept μ ν masks) :=
  by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hpowSpace : work + (512 * h + 1) ≤ lim.space :=
    by
    unfold LightLocalCoverCandidate.space at hspace
    omega
  have hmaskWork : masks + LocalMaskGraph.vertexCount (512 * h) h ≤ work := by omega
  have hbitsWork : bitPtr + LocalMaskGraph.vertexCount (512 * h) h * (512 * h) ≤ work := by omega
  have hhostWord : (LightLocalCoverHost.word h : ℤ) ≤ lim.word :=
    by
    have hb : LightLocalCoverHost.word h ≤ word h := Nat.le_add_right ..
    exact (Int.ofNat_le.mpr hb).trans hword
  have hpowerWord : ((2 ^ (512 * h + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hb : 2 ^ (512 * h + 1) ≤ word h := Nat.le_add_left ..
    exact (Int.ofNat_le.mpr hb).trans hword
  have hbudget (x : ℕ) (hx : x ≤ LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hhostWord
  have hLWord := hbudget (512 * h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  have hhWord : (h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : h ≤ 512 * h)).trans hLWord
  have hnWord :=
    hbudget (LocalMaskGraph.vertexCount (512 * h) h)
      (by
        unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hpWord :=
    hbudget (localPrime h)
      (by
        unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hcapWord :=
    hbudget (localBucketCap h)
      (by
        unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hNWord := hbudget (rows h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  apply Meets.of_body S.main
  unfold body time
  have he :=
    LightSubsetEnumerationSetup.meets (d := d + 1) (μ := μ) (L := 512 * h) (k := h) (dst := masks) (work := work) S.enum
      S.powers S.enumRec hw hpowSpace hpowerWord (by omega) hmaskWork (by omega)
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
    | refine _root_.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen he ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    on_goal -1 =>
      (rintro ve μ₁ ⟨hve, hmaskSeg, hpowers, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmaskRead₁ :
    ∀ i < LocalMaskGraph.vertexCount (512 * h) h, μ₁ (masks + i) = (LocalMaskGraph.maskAt (512 * h) h i : ℤ) :=
    by
    intro i hi
    have hi' : i < (SubsetAddress.enumerateLayer (512 * h) h).length := by
      simpa only [SubsetAddress.enumerateLayer_length, LocalMaskGraph.vertexCount] using hi
    have he := hmaskSeg i (by simpa only [List.length_map] using hi')
    simpa only [LocalMaskGraph.maskAt, List.getD_eq_getElem _ _ hi', List.getElem_map] using he
  have hmaskLt : ∀ i < LocalMaskGraph.vertexCount (512 * h) h, LocalMaskGraph.maskAt (512 * h) h i < 2 ^ (512 * h) :=
    fun _ hi => (LocalMaskGraph.maskAt_spec hi).1
  have hb :=
    LightMaskBitTable.meets (d := d + 1) (μ := μ₁) (L := 512 * h) (masks := masks) (dst := bitPtr) (n :=
      LocalMaskGraph.vertexCount (512 * h) h) (work := work) S.bits S.oneBits S.powers S.erase
      (LocalMaskGraph.maskAt (512 * h) h) hw (by omega) hpowSpace hmasks hbitsWork hpowerWord hmaskRead₁ hmaskLt
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    on_goal -1 => (rintro vb μ₂ ⟨hbitsRead, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmaskRead₂ :
    ∀ i < LocalMaskGraph.vertexCount (512 * h) h, μ₂ (masks + i) = (LocalMaskGraph.maskAt (512 * h) h i : ℤ) :=
    by
    intro i hi
    rw [hkeep₂ _ ⟨by omega, Or.inl (by omega)⟩]
    exact hmaskRead₁ i hi
  have hh :=
    S.host.meets (d := d + 1) (μ := μ₂) (h := h) (masks := masks) (bitPtr := bitPtr) (maps := maps) (raw0 := raw0)
      (raw1 := raw1) (hist0 := hist0) (hist1 := hist1) (matrixPtr := matrixPtr) (work := work) (scheduleMaps :=
      scheduleMaps) hw (by omega) hspace (by omega) hbits hmaps hraw0 hraw1 hhist0 hhist1 hmatrix hschedule houtSpace
      hhostWord hmaskRead₂ hbitsRead
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
    | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    on_goal -1 =>
      (rintro vh μ₃ ⟨hvh, hdata, hrows, hselection, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hvh, hdata, hrows, hselection, ?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (by omega), hkeep₂ a ⟨by omega, Or.inl (by omega)⟩]
  exact hkeep₁ a ⟨by omega, Or.inl ha⟩
end Procs
end ThreeSum.LightLocalCoverBuild
