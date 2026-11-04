-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedHost.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:57:40.534699+00:00
-- url     : https://prove2.me/submissions/254a046c-02b2-4c40-a758-10a46003b8e1

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourcePreparation
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCoverInput
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_getElem
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_getElem
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
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
import Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_fin
import Theorems.Thm_ThreeSum_BlockSourceTableLayout_mask_sets
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
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_left
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_right
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_5f0dc31657648884
import Definitions.Def_WeightedCache3SUM_Alias_42cdf1d3e28ca4c2
import Definitions.Def_WeightedCache3SUM_Alias_591a970b324c0271
import Theorems.Thm_ThreeSum_LightBlockSourceStages_meets_left
import Theorems.Thm_ThreeSum_LightBlockSourceStages_meets_right
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
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateDownset_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
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
open ThreeSum ThreeSum.LightBlockSourceRetainedHost
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LightSubsetAddress LightPascal LocalCoverBounds BlockSourceFlags
open BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 4000000
set_option maxRecDepth 14000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceRetainedHost
namespace Procs
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] {pMain : ℕ}
    (C : Procs P pMain) {μ : ℕ → ℤ}
    {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR masks coeff0 coeff1 rawLeft rawRight flags
      baseL baseR maskBase bitBase rowOut work : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (q : GlobalOutput h J) (vL vR : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ A) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + J * (512 * h) + 9 ≤ lim.depth)
    (hcut : cut ≤ J * (512 * h)) (hocc : occ + J ≤ masks) (hmaps : maps + 2 * (512 * h) * scheduleSize h ≤ masks)
    (hcandidates : candidates + scheduleSize h ≤ masks)
    (hleft : histL + LightLocalCoverSchedule.rows h * localPrime h ≤ masks)
    (hright : histR + LightLocalCoverSchedule.rows h * localPrime h ≤ masks)
    (hsourceHistL : sourceHistL + modulus h J ≤ masks) (hsourceHistR : sourceHistR + modulus h J ≤ masks)
    (hmasks : masks + downsetCap (J * (512 * h)) cut ≤ coeff0) (hc0 : coeff0 + J * (512 * h) ≤ coeff1)
    (hc1 : coeff1 + J * (512 * h) ≤ rawLeft) (hrawLeft : rawLeft + downsetCap (J * (512 * h)) cut ≤ rawRight)
    (hrawRight : rawRight + downsetCap (J * (512 * h)) cut ≤ flags)
    (hflags : flags + 2 * downsetCap (J * (512 * h)) cut + 2 ≤ baseL)
    (hbaseL : baseL + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut ≤ baseR)
    (hbaseR : baseR + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut ≤ maskBase)
    (hmaskBase : maskBase + downsetCap (J * (512 * h)) cut ≤ bitBase) (hbits : bitBase + J * (512 * h) ≤ rowOut)
    (hrowOut : rowOut + 2 ≤ work) (hspace : space work h J ≤ lim.space) (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ i : Fin NL, vL i.val = b (eL i)) (hinputR : ∀ i : Fin NR, vR i.val = a (eR i))
    (hhistReadL :
      ∀ r < modulus h J, μ (sourceHistL + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR :
      ∀ r < modulus h J,
        μ (sourceHistR + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ + j) = (occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J, 512 * h, h, localPrime h, localBucketCap h, cut, modulus h J, occ, maps, candidates, histL, histR,
        sourceHistL, sourceHistR, masks, coeff0, coeff1, rawLeft, rawRight, flags, baseL, baseR, maskBase, bitBase,
        rowOut, work]
      μ (time h J cut)
      (fun _ ν =>
        LightZetaStages.StoredThrough ν baseL cut (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J * (512 * h)) ∧
          LightZetaStages.StoredThrough ν baseR cut (BlockIndexedQuery.rightSource (p : ℤ) shift A a q)
              (J * (512 * h)) ∧
            Kept μ ν masks) :=
  by
  have hsEnum : work + (J * (512 * h) + 1) ≤ lim.space := (le_max_left _ _).trans hspace
  have hsRest := (le_max_right _ _).trans hspace
  have hsPrep : LightSourcePreparation.space work J (512 * h) (localPrime h) ≤ lim.space :=
    (le_max_left _ _).trans hsRest
  have hsStages : LightSourceRetainedStages.space work (J * (512 * h)) (endpointBound h J) ≤ lim.space :=
    (le_max_right _ _).trans hsRest
  have hwEnum : ((2 ^ (J * (512 * h) + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ (J * (512 * h) + 1) ≤ word NL NR h J :=
      (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwPrep :
    (LightSourcePreparation.word J (512 * h) (localPrime h) (localPrime h) ((512 * h).choose h) (localBucketCap h) :
        ℤ) ≤
      lim.word :=
    by
    have hh :
      LightSourcePreparation.word J (512 * h) (localPrime h) (localPrime h) ((512 * h).choose h) (localBucketCap h) ≤
        word NL NR h J :=
      (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwLeft : (LightSourceRetainedStages.word (J * (512 * h)) (modulus h J) (endpointBound h J) NL : ℤ) ≤ lim.word :=
    by
    have hh : LightSourceRetainedStages.word (J * (512 * h)) (modulus h J) (endpointBound h J) NL ≤ word NL NR h J :=
      (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwRight : (LightSourceRetainedStages.word (J * (512 * h)) (modulus h J) (endpointBound h J) NR : ℤ) ≤ lim.word :=
    by
    have hh : LightSourceRetainedStages.word (J * (512 * h)) (modulus h J) (endpointBound h J) NR ≤ word NL NR h J :=
      Nat.le_add_left _ _
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ) * (512 * (h : ℤ)) ≤ lim.word := by
    exact (by exact_mod_cast (show J * (512 * h) ≤ lim.space by omega) : (J : ℤ) * (512 * (h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ) * (512 * (h : ℤ)) := by positivity
  apply Meets.of_body C.main
  unfold body time
  have he :=
    LightDownsetEnumerationSetup.meets (d := d + 1) (μ := μ) (L := J * (512 * h)) (cut := cut) (dst := masks) (work :=
      work) C.enumMain C.powers C.downset C.layer hw hsEnum hwEnum hcut (by omega) (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time, LightSourcePreparation.time,
              LightSourceRetainedStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time] <;> omega)
    on_goal -1 => (rintro count ν₁ ⟨hcount, hseg, _, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst count
  have keptEnum : Kept μ ν₁ masks := by
    intro x hx
    exact kept₁ x ⟨by omega, Or.inl hx⟩
  have hcover' := hcover.of_kept keptEnum hmaps hcandidates hleft hright
  have hocc' : ∀ j < J, ν₁ (occ + j) = (occurrenceIndices (outputOccurrences q) j : ℤ) :=
    by
    intro j hj
    exact (keptEnum _ (by omega)).trans (hoccRead j hj)
  have hmaskRead :
    ∀ i < downsetCap (J * (512 * h)) cut,
      ν₁ (masks + i) = (subsetMask (indexSet (BlockSourceTableLayout.sets h J cut i)) : ℤ) :=
    by
    intro i hi
    rw [BlockSourceTableLayout.mask_sets hi, SourceTableLayout.maskAt,
      List.getD_eq_getElem _ _ (by simpa only [enumerateDownset_length] using hi)]
    exact hseg.getElem (by simpa only [enumerateDownset_length] using hi)
  have hpRun :=
    LightBlockSourcePreparation.meets (d := d + 1) (μ := ν₁) C.prepare (occ := occ) (maps := maps) (candidates :=
      candidates) (histL := histL) (histR := histR) (masks := masks) (n := downsetCap (J * (512 * h)) cut) (coeff0 :=
      coeff0) (coeff1 := coeff1) (rawLeft := rawLeft) (rawRight := rawRight) (flags := flags) (bitBase := bitBase)
      (rowOut := rowOut) (work := work) (outputOccurrences q) (BlockSourceTableLayout.sets h J cut) hw (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hc0 hc1 hrawLeft hrawRight (by omega) hbits hrowOut
      hsPrep hwPrep hocc' hcover'.candidates hcover'.leftRows hcover'.rightRows hcover'.leftCounts hcover'.rightCounts
      hmaskRead
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
    | refine _root_.Light.Ends.callToThen (hpRun _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpRun ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time, LightSourcePreparation.time,
              LightSourceRetainedStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time] <;> omega)
    on_goal -1 =>
      (rintro r ν₂ ⟨rawL, rawR, flagL, flagR, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have keptPrep : Kept μ ν₂ masks := by
    intro x hx
    exact (kept₂ x (by omega)).trans (keptEnum x hx)
  have hhL :
    ∀ r < modulus h J,
      ν₂ (sourceHistL + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ) :=
    by
    intro r hr
    exact (keptPrep _ (by omega)).trans (hhistReadL r hr)
  have hlRun :=
    LightBlockSourceRetainedStages.meets_left (d := d + 1) (μ := ν₂) C.stages (N := NL) (raw := rawLeft) (flags :=
      flags) (p := p) (table := sourceHistL) (base := baseL) (work := work) (cut := cut) (maskBase := maskBase) B b q vL
      eL hw (by omega) hcut (by omega) (by omega) (by omega) (by omega) (by omega) hsStages hwLeft hinputL hhL rawL
      flagL
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
    | refine _root_.Light.Ends.callToThen (hlRun _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hlRun ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time, LightSourcePreparation.time,
              LightSourceRetainedStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time] <;> omega)
    on_goal -1 => (rintro r ν₃ ⟨storedL, kept₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have keptLeft : Kept μ ν₃ masks := by
    intro x hx
    exact (kept₃ x (by omega)).trans (keptPrep x hx)
  have hhR :
    ∀ r < modulus h J,
      ν₃ (sourceHistR + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ) :=
    by
    intro r hr
    exact (keptLeft _ (by omega)).trans (hhistReadR r hr)
  have rawR' :
    ∀ i < downsetCap (J * (512 * h)) cut,
      ν₃ (rawRight + i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i) :=
    by
    intro i hi
    exact (kept₃ _ (by omega)).trans (rawR i hi)
  have flagR' :
    ∀ i < downsetCap (J * (512 * h)) cut,
      ν₃ (flags + downsetCap (J * (512 * h)) cut + i) =
        (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i) then 1 else 0 : ℕ) :=
    by
    intro i hi
    exact (kept₃ _ (by omega)).trans (flagR i hi)
  have hrRun :=
    LightBlockSourceRetainedStages.meets_right (d := d + 1) (μ := ν₃) C.stages (N := NR) (raw := rawRight) (flags :=
      flags + downsetCap (J * (512 * h)) cut) (p := p) (table := sourceHistR) (base := baseR) (work := work) (cut :=
      cut) (maskBase := maskBase) A a q vR eR hw (by omega) hcut (by omega) (by omega) (by omega) hbaseR (by omega)
      hsStages hwRight hinputR hhR rawR' flagR'
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
    | refine _root_.Light.Ends.callToThen (hrRun _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrRun ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time, LightSourcePreparation.time,
              LightSourceRetainedStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetEnumerationSetup.time,
            LightDownsetEnumeration.time, LightSourcePreparation.time, LightSourceRetainedStages.time] <;> omega)
    on_goal -1 => (rintro r ν₄ ⟨storedR, kept₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, storedR, ?_⟩
  · intro j hj S hS
    have hr := subsetRank_lt hS
    have hmul := Nat.mul_le_mul_right (downsetCap (J * (512 * h)) cut) (Nat.succ_le_succ hj)
    have haddr : LightZetaStages.stageBase baseL (downsetCap (J * (512 * h)) cut) j + subsetRank S < baseR := by
      calc
        LightZetaStages.stageBase baseL (downsetCap (J * (512 * h)) cut) j + subsetRank S <
            baseL + j * downsetCap (J * (512 * h)) cut + downsetCap (J * (512 * h)) cut :=
          Nat.add_lt_add_left hr _
        _ = baseL + (j + 1) * downsetCap (J * (512 * h)) cut := by ring
        _ ≤ baseL + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut := (Nat.add_le_add_left hmul _)
        _ ≤ baseR := hbaseL
    exact (kept₄ _ haddr).trans (storedL j hj S hS)
  · intro x hx
    exact (kept₄ x (by omega)).trans (keptLeft x hx)
end Procs
end ThreeSum.LightBlockSourceRetainedHost
