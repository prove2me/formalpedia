-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchStep.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:16:32.511641+00:00
-- url     : https://prove2.me/submissions/d6dce9fd-1361-492d-9056-e245ef646f87

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
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
import Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_fin
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
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_addresses_le_work
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_left_cell
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_right_cell
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_slot
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_header_end_le_slot
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_end_le_masks
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_slot_width_le_work
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_5f0dc31657648884
import Definitions.Def_WeightedCache3SUM_Alias_a7dfb79b11046052
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Definitions.Def_WeightedCache3SUM_Alias_f8e3ce9eb3f48862
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
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
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_bff01fd4b2900a53
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Definitions.Def_WeightedCache3SUM_Alias_a076d5b93ecac4d9
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
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
attribute [local simp] ThreeSum.BlockSourceFlags.candidateIndices_fin
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
attribute [local simp] ThreeSum.LightSourceRowScan.count_zero
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero
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
open ThreeSum ThreeSum.LightBlockSourceBatchStep
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceBatchStep
namespace Procs
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] {pMain : ℕ}
    (C : Procs P pMain) {μ : ℕ → ℤ}
    {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR base count i : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (q : GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B)
    (eR : Fin NR ≃ A) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + J * (512 * h) + 10 ≤ lim.depth)
    (hcut : cut ≤ J * (512 * h)) (hi : i < count) (hocc : occ + J ≤ base)
    (hmaps : maps + 2 * (512 * h) * scheduleSize h ≤ base) (hcandidates : candidates + scheduleSize h ≤ base)
    (hleft : histL + LightLocalCoverSchedule.rows h * localPrime h ≤ base)
    (hright : histR + LightLocalCoverSchedule.rows h * localPrime h ≤ base)
    (hsourceHistL : sourceHistL + modulus h J ≤ base) (hsourceHistR : sourceHistR + modulus h J ≤ base)
    (hspace :
      LightBlockSourceRetainedHost.space (LightBlockSourceBatchLayout.work base count (J * (512 * h)) cut) h J ≤
        lim.space)
    (hword : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word) (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL :
      ∀ r < modulus h J, μ (sourceHistL + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR :
      ∀ r < modulus h J,
        μ (sourceHistR + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ + j) = (occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J, 512 * h, h, localPrime h, localBucketCap h, cut, modulus h J, occ, maps, candidates, histL, histR,
        sourceHistL, sourceHistR, base, downsetCap (J * (512 * h)) cut, count,
        LightBlockSourceBatchLayout.banks base count, LightBlockSourceBatchLayout.stride (J * (512 * h)) cut,
        LightBlockSourceBatchLayout.maskBase base count (J * (512 * h)) cut,
        LightBlockSourceBatchLayout.bitBase base count (J * (512 * h)) cut,
        LightBlockSourceBatchLayout.rowOut base count (J * (512 * h)) cut,
        LightBlockSourceBatchLayout.work base count (J * (512 * h)) cut, i]
      μ (time h J cut)
      (fun _ ν =>
        LightZetaStages.StoredThrough ν (LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i) cut
            (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J * (512 * h)) ∧
          LightZetaStages.StoredThrough ν (LightBlockSourceBatchLayout.rightBase base count (J * (512 * h)) cut i) cut
              (BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J * (512 * h)) ∧
            ν (base + 2 * i) = (LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i : ℤ) ∧
              ν (base + 2 * i + 1) = (LightBlockSourceBatchLayout.rightBase base count (J * (512 * h)) cut i : ℤ) ∧
                KeptBut μ ν (LightBlockSourceBatchLayout.slot base count (J * (512 * h)) cut i) (base + 2 * i) 2) :=
  by
  have hs : LightBlockSourceBatchLayout.work base count (J * (512 * h)) cut + (J * (512 * h) + 1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwork : LightBlockSourceBatchLayout.work base count (J * (512 * h)) cut ≤ lim.space := by omega
  have hslot := LightBlockSourceBatchLayout.slot_width_le_work (base := base) (W := J * (512 * h)) (cut := cut) hi
  have hhead := LightBlockSourceBatchLayout.header_end_le_slot (base := base) (W := J * (512 * h)) (cut := cut) hi
  have hbanks := LightBlockSourceBatchLayout.banks_le_slot base count (J * (512 * h)) cut i
  have haddr := LightBlockSourceBatchLayout.addresses_le_work (base := base) (W := J * (512 * h)) (cut := cut) hi
  have hwidth : (J : ℤ) * (512 * (h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show J * (512 * h) ≤ lim.space by omega) : (J : ℤ) * (512 * (h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ) * (512 * (h : ℤ)) := by positivity
  have hwidthPlus : (J : ℤ) * (512 * (h : ℤ)) + 1 ≤ lim.word :=
    (by exact_mod_cast (show J * (512 * h) + 1 ≤ lim.space by omega) : (J : ℤ) * (512 * (h : ℤ)) + 1 ≤ lim.space).trans
      hw
  have hleftSpace : LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i ≤ lim.space := by omega
  have hrightSpace : LightBlockSourceBatchLayout.rightBase base count (J * (512 * h)) cut i ≤ lim.space := by omega
  have hprodNat : i * LightBlockSourceBatchLayout.stride (J * (512 * h)) cut ≤ lim.space :=
    by
    unfold LightBlockSourceBatchLayout.slot at hslot
    omega
  have hprod : (i : ℤ) * (LightBlockSourceBatchLayout.stride (J * (512 * h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprodNat :
          (i : ℤ) * (LightBlockSourceBatchLayout.stride (J * (512 * h)) cut : ℤ) ≤ lim.space).trans
      hw
  have hprodNonneg : (0 : ℤ) ≤ (i : ℤ) * (LightBlockSourceBatchLayout.stride (J * (512 * h)) cut : ℤ) := by positivity
  have htwocapNat : 2 * downsetCap (J * (512 * h)) cut ≤ lim.space :=
    by
    unfold LightBlockSourceBatchLayout.leftBase at hleftSpace
    omega
  have htwocap : (2 : ℤ) * (downsetCap (J * (512 * h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast htwocapNat : (2 : ℤ) * (downsetCap (J * (512 * h)) cut : ℤ) ≤ lim.space).trans hw
  have hfamNat : (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut ≤ lim.space :=
    by
    unfold LightBlockSourceBatchLayout.rightBase LightBlockSourceBatchLayout.family at hrightSpace
    omega
  have hfam : ((J : ℤ) * (512 * (h : ℤ)) + 1) * (downsetCap (J * (512 * h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hfamNat :
          ((J : ℤ) * (512 * (h : ℤ)) + 1) * (downsetCap (J * (512 * h)) cut : ℤ) ≤ lim.space).trans
      hw
  have hfamNonneg : (0 : ℤ) ≤ ((J : ℤ) * (512 * (h : ℤ)) + 1) * (downsetCap (J * (512 * h)) cut : ℤ) := by positivity
  have hbase : base ≤ LightBlockSourceBatchLayout.slot base count (J * (512 * h)) cut i :=
    by
    unfold LightBlockSourceBatchLayout.banks at hbanks
    omega
  have hs0 :
    LightBlockSourceBatchLayout.banks base count + i * LightBlockSourceBatchLayout.stride (J * (512 * h)) cut ≤
      lim.space :=
    by
    unfold LightBlockSourceBatchLayout.slot at hslot
    omega
  have hs1 :
    LightBlockSourceBatchLayout.slot base count (J * (512 * h)) cut i + downsetCap (J * (512 * h)) cut ≤ lim.space :=
    haddr.1.trans hwork
  have hs2 : LightBlockSourceBatchLayout.coeff0 base count (J * (512 * h)) cut i + J * (512 * h) ≤ lim.space :=
    haddr.2.1.trans hwork
  have hs3 : LightBlockSourceBatchLayout.coeff1 base count (J * (512 * h)) cut i + J * (512 * h) ≤ lim.space :=
    haddr.2.2.1.trans hwork
  have hs4 :
    LightBlockSourceBatchLayout.rawLeft base count (J * (512 * h)) cut i + downsetCap (J * (512 * h)) cut ≤ lim.space :=
    haddr.2.2.2.1.trans hwork
  have hs5 :
    LightBlockSourceBatchLayout.rawRight base count (J * (512 * h)) cut i + downsetCap (J * (512 * h)) cut ≤
      lim.space :=
    haddr.2.2.2.2.1.trans hwork
  have hs6 :
    LightBlockSourceBatchLayout.flags base count (J * (512 * h)) cut i + 2 * downsetCap (J * (512 * h)) cut + 2 ≤
      lim.space :=
    haddr.2.2.2.2.2.1.trans hwork
  have hs7 :
    LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i +
        (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut ≤
      lim.space :=
    haddr.2.2.2.2.2.2.trans hwork
  have hs2Int :
    (LightBlockSourceBatchLayout.coeff0 base count (J * (512 * h)) cut i : ℤ) + (J : ℤ) * (512 * (h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast hs2 :
          (LightBlockSourceBatchLayout.coeff0 base count (J * (512 * h)) cut i : ℤ) + (J : ℤ) * (512 * (h : ℤ)) ≤
            lim.space).trans
      hw
  have hs3Int :
    (LightBlockSourceBatchLayout.coeff1 base count (J * (512 * h)) cut i : ℤ) + (J : ℤ) * (512 * (h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast hs3 :
          (LightBlockSourceBatchLayout.coeff1 base count (J * (512 * h)) cut i : ℤ) + (J : ℤ) * (512 * (h : ℤ)) ≤
            lim.space).trans
      hw
  have hs7Int :
    (LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i : ℤ) +
        ((J : ℤ) * (512 * (h : ℤ)) + 1) * (downsetCap (J * (512 * h)) cut : ℤ) ≤
      lim.word :=
    (by exact_mod_cast hs7 :
          (LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i : ℤ) +
              ((J : ℤ) * (512 * (h : ℤ)) + 1) * (downsetCap (J * (512 * h)) cut : ℤ) ≤
            lim.space).trans
      hw
  apply Meets.of_body C.main
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
    refine _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.slot base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.slot]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.slot] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.slot] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.coeff0 base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.coeff0]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.coeff0] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.coeff0] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.coeff1 base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.coeff1]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.coeff1] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.coeff1] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.rawLeft base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.rawLeft]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.rawLeft] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.rawLeft] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.rawRight base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.rawRight]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.rawRight] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.rawRight] <;> omega)
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
    refine _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.flags base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.flags]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.flags] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.flags] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.leftBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.leftBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.leftBase] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightBlockSourceBatchLayout.rightBase base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceBatchLayout.rightBase,
            LightBlockSourceBatchLayout.family]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceBatchLayout.rightBase, LightBlockSourceBatchLayout.family] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceBatchLayout.rightBase,
            LightBlockSourceBatchLayout.family] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hrun :=
    C.source.meets (d := d + 1) (μ := μ) (cut := cut) (p := p) (shift := shift) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (sourceHistL := sourceHistL) (sourceHistR :=
      sourceHistR) (masks := LightBlockSourceBatchLayout.slot base count (J * (512 * h)) cut i) (coeff0 :=
      LightBlockSourceBatchLayout.coeff0 base count (J * (512 * h)) cut i) (coeff1 :=
      LightBlockSourceBatchLayout.coeff1 base count (J * (512 * h)) cut i) (rawLeft :=
      LightBlockSourceBatchLayout.rawLeft base count (J * (512 * h)) cut i) (rawRight :=
      LightBlockSourceBatchLayout.rawRight base count (J * (512 * h)) cut i) (flags :=
      LightBlockSourceBatchLayout.flags base count (J * (512 * h)) cut i) (baseL :=
      LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i) (baseR :=
      LightBlockSourceBatchLayout.rightBase base count (J * (512 * h)) cut i) (maskBase :=
      LightBlockSourceBatchLayout.maskBase base count (J * (512 * h)) cut) (bitBase :=
      LightBlockSourceBatchLayout.bitBase base count (J * (512 * h)) cut) (rowOut :=
      LightBlockSourceBatchLayout.rowOut base count (J * (512 * h)) cut) (work :=
      LightBlockSourceBatchLayout.work base count (J * (512 * h)) cut) B b A a q vL vR eL eR hw (by omega) hcut
      (hocc.trans hbase) (hmaps.trans hbase) (hcandidates.trans hbase) (hleft.trans hbase) (hright.trans hbase)
      (hsourceHistL.trans hbase) (hsourceHistR.trans hbase) le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      (LightBlockSourceBatchLayout.right_end_le_masks hi) le_rfl le_rfl le_rfl hspace hword hinputL hinputR hhistReadL
      hhistReadR hoccRead hcover
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
    | refine _root_.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro r ν ⟨storedL, storedR, kept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine
      _root_.Light.Ends.storeToThen (base + 2 * i)
        (LightBlockSourceBatchLayout.leftBase base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
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
    refine
      _root_.Light.Ends.storeToThen (base + 2 * i + 1)
        (LightBlockSourceBatchLayout.rightBase base count (J * (512 * h)) cut i : ℕ) ?_ ?_ ?_
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
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj S hS
    have hb := LightBlockSourceBatchLayout.banks_le_left_cell base count (J * (512 * h)) cut i j S
    unfold LightBlockSourceBatchLayout.banks at hb
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact storedL j hj S hS
  · intro j hj S hS
    have hb := LightBlockSourceBatchLayout.banks_le_right_cell base count (J * (512 * h)) cut i j S
    unfold LightBlockSourceBatchLayout.banks at hb
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact storedR j hj S hS
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · exact Function.update_self ..
  · intro x hx
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact kept x hx.1
end Procs
end ThreeSum.LightBlockSourceBatchStep
