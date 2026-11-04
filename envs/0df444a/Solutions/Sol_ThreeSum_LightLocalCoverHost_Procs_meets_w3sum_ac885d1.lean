-- Prove2me | solution 1 for ThreeSum.LightLocalCoverHost.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:22:50.507551+00:00
-- url     : https://prove2.me/submissions/0a066d59-a4e0-4ea1-8873-72fb65e5bb1e

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Definitions.Def_Submission_ThreeSum_LightWeightGather
import Definitions.Def_Submission_ThreeSum_LightLocalCoverHost
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
import Theorems.Thm_ThreeSum_BooleanGreedy_choices_length
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
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_lt
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_length
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_rows_pos
import Definitions.Def_WeightedCache3SUM_Alias_6914da8a0e9a7f49
import Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_matrix_read
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Theorems.Thm_ThreeSum_LightLocalCoverTables_coeff_digit
import Theorems.Thm_ThreeSum_LightMaskBits_bit_le
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
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalCoverMatrix_entry_le
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_spec
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
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
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverHost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverHost
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * h + 6 ≤ lim.depth)
    (hspace :
      LightLocalCoverCandidate.space work (512 * h) (LocalMaskGraph.vertexCount (512 * h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks + LocalMaskGraph.vertexCount (512 * h) h ≤ maps)
    (hbits : bitPtr + LocalMaskGraph.vertexCount (512 * h) h * (512 * h) ≤ maps)
    (hmaps : maps + rows h * (2 * (512 * h)) ≤ raw0) (hraw0 : raw0 + 2 * LocalMaskGraph.vertexCount (512 * h) h ≤ raw1)
    (hraw1 : raw1 + 2 * LocalMaskGraph.vertexCount (512 * h) h ≤ hist0) (hhist0 : hist0 + rows h * localPrime h ≤ hist1)
    (hhist1 : hist1 + rows h * localPrime h ≤ matrixPtr) (hmatrix : matrixPtr + rows h * cols h ≤ work)
    (hschedule : work + LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps + scheduleSize h * (2 * (512 * h)) ≤ lim.space) (hword : (word h : ℤ) ≤ lim.word)
    (hmaskRead :
      ∀ i < LocalMaskGraph.vertexCount (512 * h) h, μ (masks + i) = (LocalMaskGraph.maskAt (512 * h) h i : ℤ))
    (hbitsRead :
      ∀ i < LocalMaskGraph.vertexCount (512 * h) h,
        ∀ j < 512 * h, μ (bitPtr + i * (512 * h) + j) = (LocalCoverMatrix.bits (512 * h) h i j : ℤ)) :
    Meets lim P pMain d
      [512 * h, localPrime h, rows h, LocalMaskGraph.vertexCount (512 * h) h, localBucketCap h, masks, bitPtr, maps,
        raw0, raw1, hist0, hist1, matrixPtr, work, scheduleSize h, scheduleMaps]
      μ (time h)
      (fun r ν =>
        r = (scheduleMaps : ℤ) ∧
          Data ν h maps hist0 hist1 matrixPtr ∧
            ScheduleRows ν h scheduleMaps ∧
              (∀ s : Occurrence h, ν (LightCoverGreedy.out work (rows h) (cols h) + s.val) = (candidateAt h s : ℤ)) ∧
                Kept μ ν maps) :=
  by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hscheduleWork : work ≤ scheduleMaps := by omega
  have hbudget (x : ℕ) (hx : x ≤ word h) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hmatrixWord :=
    hbudget
      (LightLocalCoverCandidate.word (512 * h) (LocalMaskGraph.vertexCount (512 * h) h) (localPrime h)
        (localBucketCap h) (rows h))
      (by unfold word; omega)
  have hgatherWord := hbudget (LightWeightGather.word (rows h) (scheduleSize h) (2 * (512 * h))) (by unfold word; omega)
  have hLWord := hbudget (512 * h) (by unfold word LightWeightGather.word; omega)
  have hWWord := hbudget (2 * (512 * h)) (by unfold word LightWeightGather.word; omega)
  have hWWordZ : (2 : ℤ) * (512 * (h : ℤ)) ≤ lim.word := by exact_mod_cast hWWord
  have h2Word :=
    hbudget 2
      (by
        unfold word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hpWord :=
    hbudget (localPrime h)
      (by
        unfold word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hp2Word :=
    hbudget (localPrime h * localPrime h)
      (by
        unfold word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hp2WordZ : (localPrime h : ℤ) * localPrime h ≤ lim.word := by exact_mod_cast hp2Word
  have hNWord := hbudget (rows h) (by unfold word LightWeightGather.word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold word LightWeightGather.word; omega)
  have hnWord :=
    hbudget (LocalMaskGraph.vertexCount (512 * h) h)
      (by
        unfold word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hcapWord :=
    hbudget (localBucketCap h)
      (by
        unfold word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hn : 0 < LocalMaskGraph.vertexCount (512 * h) h := Nat.choose_pos (by omega)
  have hmapsWork : maps + rows h * (2 * (512 * h)) ≤ work := by omega
  have hhist0Work : hist0 + rows h * localPrime h ≤ work := by omega
  have hhist1Work : hist1 + rows h * localPrime h ≤ work := by omega
  have hgreedySpace : work + LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ lim.space := by omega
  have houtEnd : LightCoverGreedy.out work (rows h) (cols h) + scheduleSize h ≤ scheduleMaps :=
    by
    unfold LightCoverGreedy.out LightCoverGreedy.total at *
    omega
  have hm :=
    S.matrix.meets (d := d + 1) (μ := μ) (L := 512 * h) (n := LocalMaskGraph.vertexCount (512 * h) h) (p :=
      localPrime h) (cap := localBucketCap h) (N := rows h) (masks := masks) (bitPtr := bitPtr) (maps := maps) (raw0 :=
      raw0) (raw1 := raw1) (hist0 := hist0) (hist1 := hist1) (dst := matrixPtr) (work := work)
      (LocalMaskGraph.maskAt (512 * h) h) (LocalCoverMatrix.bits (512 * h) h)
      (fun j => LocalMaskHashes.coeff false (candidate h j)) (fun j => LocalMaskHashes.coeff true (candidate h j)) hw
      (by omega) (localPrime_pos h) hn hspace hmasks hbits hmaps hraw0 hraw1 hhist0 hhist1 hmatrix hmatrixWord hmaskRead
      (fun _ hi => (LocalMaskGraph.maskAt_spec hi).1) hbitsRead
      (fun i _ j _ => LightMaskBits.bit_le (512 * h) (LocalMaskGraph.maskAt (512 * h) h i) j)
      (by intro j _ i hi; simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using coeff_digit h j false ⟨i, hi⟩)
      (by intro j _ i hi; simpa only [ite_true] using coeff_digit h j true ⟨i, hi⟩)
  apply Meets.of_body S.main
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
    | refine _root_.Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hm ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro vm μ₁ ⟨hdata₁, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have H₁ : Data μ₁ h maps hist0 hist1 matrixPtr := hdata₁
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (localPrime h * localPrime h : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hg :=
    S.greedy.meets (d := d + 1) (μ := μ₁) (src := matrixPtr) (activePtr := work) (rows := rows h) (cols := cols h)
      (rounds := scheduleSize h) (LightLocalCoverSchedule.matrix h) hw (by omega) (rows_pos h) hmatrix hgreedySpace
      (fun _ hi _ hr => H₁.matrix_read hi hr) (fun _ _ _ _ => LocalCoverMatrix.entry_le ..) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, cols]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, cols] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, cols] <;> omega)
    on_goal -1 =>
      (rintro vg μ₂ ⟨hvg, hchoices, hactive, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have H₂ : Data μ₂ h maps hist0 hist1 matrixPtr :=
    H₁.of_kept (fun a ha => hkeep₂ a (Or.inl ha)) hmapsWork hhist0Work hhist1Work hmatrix
  have hselection :
    ∀ s < scheduleSize h, μ₂ (LightCoverGreedy.out work (rows h) (cols h) + s) = ((indices h).getD s 0 : ℤ) :=
    by
    intro s hs
    have hs' : s < (indices h).length := by rw [indices_length]; exact hs
    have hr := hchoices s (by simpa only [List.length_map, BooleanGreedy.choices_length] using hs)
    rw [List.getD_eq_getElem _ _ hs']
    simpa only [List.getElem_map, indices] using hr
  have hselectionLt : ∀ s < scheduleSize h, (indices h).getD s 0 < rows h :=
    by
    intro s hs
    exact candidateAt_lt h ⟨s, hs⟩
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (2 * (512 * h) : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hc :=
    S.gather.meets (d := d + 1) (μ := μ₂) (indices := LightCoverGreedy.out work (rows h) (cols h)) (src := maps) (dst :=
      scheduleMaps) (N := rows h) (rows := scheduleSize h) (width := 2 * (512 * h)) (fun s => (indices h).getD s 0) hw
      (by omega) houtEnd (by omega) houtSpace hgatherWord hselectionLt hselection
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hvg, LightCoverGreedy.out, cols]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, hvg, LightCoverGreedy.out, cols] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hvg, LightCoverGreedy.out, cols] <;> omega)
    on_goal -1 => (rintro vc μ₃ ⟨hcopy, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have H₃ : Data μ₃ h maps hist0 hist1 matrixPtr :=
    H₂.of_kept (fun a ha => hkeep₃ a (Or.inl (by omega))) hmapsWork hhist0Work hhist1Work hmatrix
  have hrows₃ : ScheduleRows μ₃ h scheduleMaps := H₂.gathered_schedule hcopy
  have hselection₃ :
    ∀ s : Occurrence h, μ₃ (LightCoverGreedy.out work (rows h) (cols h) + s.val) = (candidateAt h s : ℤ) :=
    by
    intro s
    rw [hkeep₃ _ (Or.inl (by have hs := s.isLt; omega))]
    exact hselection s.val s.isLt
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (scheduleMaps : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, H₃, hrows₃, hselection₃, ?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (Or.inl (by omega)), hkeep₂ a (Or.inl (by omega))]
  exact hkeep₁ a ha
end Procs
end ThreeSum.LightLocalCoverHost
