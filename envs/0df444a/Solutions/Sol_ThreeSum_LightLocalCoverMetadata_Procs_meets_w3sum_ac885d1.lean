-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMetadata.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:43.03639+00:00
-- url     : https://prove2.me/submissions/9982bdb3-9307-448b-8aad-29edbc70c24e

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMetadata
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Definitions.Def_WeightedCache3SUM_Alias_5c7a134a153cf44a
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
import Definitions.Def_WeightedCache3SUM_Alias_2311045817689c86
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Theorems.Thm_ThreeSum_LightLocalCoverLayout_schedule_end_le_space
import Theorems.Thm_ThreeSum_LightLocalCoverLayout_work_le_space
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_0a77a2090c5d3d77
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
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
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
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
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverMetadata
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
open LightLocalCoverSetup (word)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8500
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverMetadata
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {base h dst : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 2 ≤ lim.depth) (hout : dst + 12 ≤ base) (hspace : space base h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h, localPrime h, vertices h, base, dst] μ (time h)
      (fun r ν => r = (nextFree base h : ℤ) ∧ Seg ν dst (values base h) ∧ SameOutside μ ν dst 12) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ word h) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hbuildWord := hbudget (LightLocalCoverBuild.word h) (by unfold word; omega)
  have h1024Word := hbudget 1024 (by unfold word; omega)
  have hLWord := hbudget (512 * h) (by unfold word; omega)
  have hNWord := hbudget (rows h) (by unfold word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold word; omega)
  have hcolsWord := hbudget (cols h) (by unfold word; omega)
  have hlogWord := hbudget (2 * cols h + 2) (by unfold word; omega)
  have hhostLe : LightLocalCoverHost.word h ≤ word h :=
    by
    have hfirst : LightLocalCoverHost.word h ≤ LightLocalCoverBuild.word h := Nat.le_add_right ..
    have hsecond : LightLocalCoverBuild.word h ≤ word h := by unfold word; omega
    exact hfirst.trans hsecond
  have hcoreBudget (x : ℕ) (hx : x ≤ LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word := hbudget x (hx.trans hhostLe)
  have hwidthWord :=
    hcoreBudget (2 * (512 * h))
      (by
        unfold LightLocalCoverHost.word LightWeightGather.word
        omega)
  have hnWord :=
    hcoreBudget (vertices h)
      (by
        unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word vertices
        omega)
  have hpWord :=
    hcoreBudget (localPrime h)
      (by
        unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hcapWord :=
    hcoreBudget (localBucketCap h)
      (by
        unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
        omega)
  have hwidthWordZ : (2 : ℤ) * (512 * (h : ℤ)) ≤ lim.word := by exact_mod_cast hwidthWord
  have hLWordZ : (512 : ℤ) * h ≤ lim.word := by exact_mod_cast hLWord
  have hp2WordZ : (localPrime h : ℤ) * localPrime h ≤ lim.word := by simpa only [cols, Nat.cast_mul] using hcolsWord
  have hcolsEq : (cols h : ℤ) = (localPrime h : ℤ) * localPrime h := by simp only [cols, Nat.cast_mul]
  have hp2Nonneg : (0 : ℤ) ≤ (localPrime h : ℤ) * localPrime h := by positivity
  have hlogBound : Nat.log2 (localPrime h ^ 2) ≤ cols h :=
    by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_le_self 2 (localPrime h ^ 2)).trans (by simp [cols, pow_two])
  have hlogResultWord : ((Nat.log2 (localPrime h ^ 2) + 1 : ℕ) : ℤ) ≤ lim.word :=
    by
    apply hbudget
    unfold word
    omega
  have hscale : 320 * (2 * h + 1) ≤ scheduleSize h :=
    by
    change 320 * (2 * h + 1) ≤ 320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1)
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hscaleWord : ((320 * (2 * h + 1) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hscale).trans hTWord
  have hscaleWordZ : (320 : ℤ) * (2 * (h : ℤ) + 1) ≤ lim.word := by exact_mod_cast hscaleWord
  have hroundWordZ : (320 : ℤ) * (2 * (h : ℤ) + 1) * (Nat.log2 (localPrime h ^ 2) + 1) ≤ lim.word := by
    simpa only [scheduleSize, LocalHashMoments.scheduleLength, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hTWord
  have hroundNonneg : (0 : ℤ) ≤ 320 * (2 * (h : ℤ) + 1) * (Nat.log2 (localPrime h ^ 2) + 1) := by positivity
  have hworkSpace : work base h ≤ lim.space := (work_le_space base h).trans hspace
  have hschedSpace : scheduleMaps base h + scheduleSize h * (2 * (512 * h)) ≤ lim.space :=
    (schedule_end_le_space base h).trans hspace
  have hsmall (x : ℕ) (hx : x ≤ work base h) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hx.trans hworkSpace)).trans hw
  have hbitPtr :=
    hsmall (bitPtr base h)
      (by
        unfold work matrixPtr hist1 hist0 raw1 raw0 maps
        omega)
  have hmaps := hsmall (maps base h) (by unfold work matrixPtr hist1 hist0 raw1 raw0; omega)
  have hraw0 := hsmall (raw0 base h) (by unfold work matrixPtr hist1 hist0 raw1; omega)
  have hraw1 := hsmall (raw1 base h) (by unfold work matrixPtr hist1 hist0; omega)
  have hhist0 := hsmall (hist0 base h) (by unfold work matrixPtr hist1; omega)
  have hhist1 := hsmall (hist1 base h) (by unfold work matrixPtr; omega)
  have hmatrix := hsmall (matrixPtr base h) (by unfold work; omega)
  have hwork := hsmall (work base h) le_rfl
  have hbase := hsmall base (by unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr; omega)
  have hprodBits :=
    hsmall (vertices h * (512 * h))
      (by
        unfold work matrixPtr hist1 hist0 raw1 raw0 maps
        omega)
  have hprodRows :=
    hsmall (rows h * (2 * (512 * h)))
      (by
        unfold work matrixPtr hist1 hist0 raw1 raw0
        omega)
  have hprodRaw := hsmall (2 * vertices h) (by unfold work matrixPtr hist1 hist0; omega)
  have hprodHist := hsmall (rows h * localPrime h) (by unfold work matrixPtr hist1; omega)
  have hprodMatrix := hsmall (rows h * cols h) (by unfold work; omega)
  have hprodBitsZ : (vertices h : ℤ) * (512 * (h : ℤ)) ≤ lim.word := by exact_mod_cast hprodBits
  have hprodRowsZ : (rows h : ℤ) * (2 * (512 * (h : ℤ))) ≤ lim.word := by exact_mod_cast hprodRows
  have hprodHistZ : (rows h : ℤ) * localPrime h ≤ lim.word := by exact_mod_cast hprodHist
  have hprodMatrixZ : (rows h : ℤ) * ((localPrime h : ℤ) * localPrime h) ≤ lim.word := by
    simpa only [cols, Nat.cast_mul] using hprodMatrix
  have hbitPtrZ : (base : ℤ) + vertices h ≤ lim.word := by simpa only [bitPtr, Nat.cast_add] using hbitPtr
  have hmapsZ : (bitPtr base h : ℤ) + (vertices h : ℤ) * (512 * (h : ℤ)) ≤ lim.word := by
    simpa only [maps, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmaps
  have hraw0Z : (maps base h : ℤ) + (rows h : ℤ) * (2 * (512 * (h : ℤ))) ≤ lim.word := by
    simpa only [raw0, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hraw0
  have hraw1Z : (raw0 base h : ℤ) + 2 * (vertices h : ℤ) ≤ lim.word := by
    simpa only [raw1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hraw1
  have hhist0Z : (raw1 base h : ℤ) + 2 * (vertices h : ℤ) ≤ lim.word := by
    simpa only [hist0, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hhist0
  have hhist1Z : (hist0 base h : ℤ) + (rows h : ℤ) * localPrime h ≤ lim.word := by
    simpa only [hist1, Nat.cast_add, Nat.cast_mul] using hhist1
  have hmatrixZ : (hist1 base h : ℤ) + (rows h : ℤ) * localPrime h ≤ lim.word := by
    simpa only [matrixPtr, Nat.cast_add, Nat.cast_mul] using hmatrix
  have hworkZ : (matrixPtr base h : ℤ) + (rows h : ℤ) * ((localPrime h : ℤ) * localPrime h) ≤ lim.word := by
    simpa only [work, cols, Nat.cast_add, Nat.cast_mul] using hwork
  have hbitsNonneg : (0 : ℤ) ≤ (vertices h : ℤ) * (512 * (h : ℤ)) := by positivity
  have hrowsNonneg : (0 : ℤ) ≤ (rows h : ℤ) * (2 * (512 * (h : ℤ))) := by positivity
  have hhistNonneg : (0 : ℤ) ≤ (rows h : ℤ) * localPrime h := by positivity
  have hmatrixNonneg : (0 : ℤ) ≤ (rows h : ℤ) * ((localPrime h : ℤ) * localPrime h) := by positivity
  have hscheduleWord : (scheduleMaps base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : scheduleMaps base h ≤ lim.space)).trans hw
  have hscheduleWordZ :
    (work base h : ℤ) + (localPrime h : ℤ) * localPrime h + (rows h : ℤ) + (scheduleSize h : ℤ) ≤ lim.word := by
    simpa only [scheduleMaps, LightCoverGreedy.total, cols, Nat.cast_add, Nat.cast_mul, Int.add_assoc] using
      hscheduleWord
  have hscheduleWork : work base h + cols h + rows h + scheduleSize h = scheduleMaps base h :=
    by
    unfold scheduleMaps LightCoverGreedy.total
    omega
  have hbaseSpace : base ≤ lim.space :=
    by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr at hworkSpace
    omega
  have hcandidateSpace : candidates base h ≤ lim.space :=
    by
    unfold candidates LightCoverGreedy.out scheduleMaps LightCoverGreedy.total at *
    omega
  have hcandidateWord : (candidates base h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hcandidateSpace).trans hw
  have hcandidateWordZ : (work base h : ℤ) + (localPrime h : ℤ) * localPrime h + (rows h : ℤ) ≤ lim.word := by
    simpa only [candidates, LightCoverGreedy.out, cols, Nat.cast_add, Nat.cast_mul] using hcandidateWord
  have hnextWord : (nextFree base h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hschedSpace).trans hw
  have hnextWordZ : (scheduleMaps base h : ℤ) + (scheduleSize h : ℤ) * (2 * (512 * (h : ℤ))) ≤ lim.word := by
    simpa only [nextFree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hnextWord
  have hproductWordZ : (scheduleSize h : ℤ) * (2 * (512 * (h : ℤ))) ≤ lim.word :=
    by
    have hm : scheduleSize h * (2 * (512 * h)) ≤ lim.space := by omega
    exact (by exact_mod_cast hm : (scheduleSize h : ℤ) * (2 * (512 * (h : ℤ))) ≤ lim.space).trans hw
  have hproductNonneg : (0 : ℤ) ≤ (scheduleSize h : ℤ) * (2 * (512 * (h : ℤ))) := by positivity
  have htwoWord : ((2 * h : ℕ) : ℤ) ≤ lim.word := by omega
  have htwoWordZ : (2 : ℤ) * h ≤ lim.word := by exact_mod_cast htwoWord
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
    refine _root_.Light.Ends.setToThen (512 * h : ℕ) ?_ ?_ ?_
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
  have hpowers : ∀ e ≤ 2 * (512 * h), (((localPrime h) ^ e : ℕ) : ℤ) ≤ lim.word :=
    by
    intro e he
    have hp : (localPrime h) ^ e ≤ rows h := Nat.pow_le_pow_right (localPrime_pos h) he
    exact (Int.ofNat_le.mpr hp).trans hNWord
  have hpower := LightNatPower.meets (d := d + 1) (b := localPrime h) (e := 2 * (512 * h)) S.power μ hwidthWord hpowers
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
    | refine _root_.Light.Ends.callToThen (hpower _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpower ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro vc μ₁ ⟨hvc, hmem₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  have hvc' : vc = (rows h : ℤ) := hvc
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (cols h : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, cols] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hl := log2_meets (d := d + 1) (x := cols h) S.log μ hlogWord
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
    on_goal -1 => (rintro vl μ₂ ⟨hvl, hmem₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  have hvl' : vl = (Nat.log2 (localPrime h ^ 2) : ℤ) := by simpa only [Nat.log2_eq_log_two, pow_two, cols] using hvl
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (scheduleSize h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hvl', scheduleSize,
            LocalHashMoments.scheduleLength]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, hvl', scheduleSize, LocalHashMoments.scheduleLength] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hvl', scheduleSize,
            LocalHashMoments.scheduleLength] <;> omega)
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
    refine _root_.Light.Ends.setToThen (bitPtr base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, bitPtr]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, bitPtr] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, bitPtr] <;> omega)
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
    refine _root_.Light.Ends.setToThen (maps base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, maps]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, maps] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, maps] <;> omega)
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
    refine _root_.Light.Ends.setToThen (raw0 base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, raw0, hvc']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, raw0, hvc'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, raw0, hvc'] <;> omega)
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
    refine _root_.Light.Ends.setToThen (raw1 base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, raw1]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, raw1] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, raw1] <;> omega)
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
    refine _root_.Light.Ends.setToThen (hist0 base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hist0]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, hist0] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hist0] <;> omega)
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
    refine _root_.Light.Ends.setToThen (hist1 base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hist1, hvc']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, hist1, hvc'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hist1, hvc'] <;> omega)
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
    refine _root_.Light.Ends.setToThen (matrixPtr base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, matrixPtr, hvc']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, matrixPtr, hvc'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, matrixPtr, hvc'] <;> omega)
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
    refine _root_.Light.Ends.setToThen (work base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, work, hvc', cols]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, work, hvc', cols] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, work, hvc', cols] <;> omega)
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
    refine _root_.Light.Ends.setToThen (scheduleMaps base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hscheduleWork, hvc', cols]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, hscheduleWork, hvc', cols] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hscheduleWork, hvc', cols] <;> omega)
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
    refine _root_.Light.Ends.setToThen (candidates base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, candidates, LightCoverGreedy.out,
            hvc', cols]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, candidates, LightCoverGreedy.out, hvc', cols] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, candidates, LightCoverGreedy.out, hvc',
            cols] <;> omega)
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
    refine _root_.Light.Ends.setToThen (nextFree base h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, nextFree]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, nextFree] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, nextFree] <;> omega)
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
    refine _root_.Light.Ends.setToThen (2 * h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen dst (512 * h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 1) (2 * h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 2) (scheduleSize h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 3) (rows h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hvc']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, hvc'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hvc'] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (dst + 4) (scheduleMaps base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 5) (candidates base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 6) (hist0 base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 7) (hist1 base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 8) (maps base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 9) (matrixPtr base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 10) (nextFree base h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 11) (cols h : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (nextFree base h : ℕ) ?_ ?_ ?_
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
  refine ⟨rfl, ?_, ?_⟩
  · have hn : Seg μ dst [] := Seg.nil
    simpa [values] using
      ((((((((((((hn.snoc (512 * h : ℕ)).snoc (2 * h : ℕ)).snoc (scheduleSize h : ℕ)).snoc (rows h : ℕ)).snoc
                                    (scheduleMaps base h : ℕ)).snoc
                                (candidates base h : ℕ)).snoc
                            (hist0 base h : ℕ)).snoc
                        (hist1 base h : ℕ)).snoc
                    (maps base h : ℕ)).snoc
                (matrixPtr base h : ℕ)).snoc
            (nextFree base h : ℕ)).snoc
        (cols h : ℕ))
  · have hp : SameOutside μ μ dst 12 := SameOutside.refl
    exact
      ((((((((((((hp.update (by omega : dst ≤ dst ∧ dst < dst + 12) (512 * h : ℕ)).update
                                                (by omega : dst ≤ dst + 1 ∧ dst + 1 < dst + 12) (2 * h : ℕ)).update
                                            (by omega : dst ≤ dst + 2 ∧ dst + 2 < dst + 12) (scheduleSize h : ℕ)).update
                                        (by omega : dst ≤ dst + 3 ∧ dst + 3 < dst + 12) (rows h : ℕ)).update
                                    (by omega : dst ≤ dst + 4 ∧ dst + 4 < dst + 12) (scheduleMaps base h : ℕ)).update
                                (by omega : dst ≤ dst + 5 ∧ dst + 5 < dst + 12) (candidates base h : ℕ)).update
                            (by omega : dst ≤ dst + 6 ∧ dst + 6 < dst + 12) (hist0 base h : ℕ)).update
                        (by omega : dst ≤ dst + 7 ∧ dst + 7 < dst + 12) (hist1 base h : ℕ)).update
                    (by omega : dst ≤ dst + 8 ∧ dst + 8 < dst + 12) (maps base h : ℕ)).update
                (by omega : dst ≤ dst + 9 ∧ dst + 9 < dst + 12) (matrixPtr base h : ℕ)).update
            (by omega : dst ≤ dst + 10 ∧ dst + 10 < dst + 12) (nextFree base h : ℕ)).update
        (by omega : dst ≤ dst + 11 ∧ dst + 11 < dst + 12) (cols h : ℕ))
end Procs
end ThreeSum.LightLocalCoverMetadata
