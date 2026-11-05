-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:51:58.1264+00:00
-- url     : https://prove2.me/submissions/90b86221-5e52-4644-8e96-6d1f0315e91a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDigitLength
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalDigitLength_clog_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalDigitLength_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 3000000
variable {lim : Limits} {depth : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
theorem _root_.solution {M b p K n U dst : ℕ} [Fact p.Prime] (μ : ℕ → ℤ) (hM : 1 < M) (hb : 1 < b) (hn : 0 < n)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst + 4 ≤ lim.space) (hdepth : depth + 1 < lim.depth)
    (hword : (word M b p K n U : ℤ) ≤ lim.word) :
    Meets lim (program M b p K) 0 depth [n, U, dst] μ (time M b p K n U)
      (fun z ν =>
        z = ((p ^ (dim M b p K n U) : ℕ) : ℤ) ∧
          Seg ν dst [(r M n : ℤ), J M b n U, dim M b p K n U, (p ^ (dim M b p K n U) : ℕ)] ∧ Kept μ ν dst) :=
  by
  have hbudget (v : ℕ) (hv : v ≤ word M b p K n U) : (v : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hv).trans hword
  have hMword := hbudget (LightWeightedGlobalDigitLength.word M (n ^ 2)) (by unfold word; omega)
  have hBword : ((LightWeightedGlobalDigitLength.word b (4 * U + 1) + r M n + 4 : ℕ) : ℤ) ≤ lim.word :=
    by
    apply hbudget
    unfold word
    omega
  have hPword :=
    hbudget (LightWeightedGlobalDigitLength.word p (8 * (J M b n U + 3) * p ^ (4 * K))) (by unfold word; omega)
  have hMliteral : (M : ℤ) ≤ lim.word := by unfold LightWeightedGlobalDigitLength.word at hMword; omega
  have hBliteral : (b : ℤ) ≤ lim.word := by unfold LightWeightedGlobalDigitLength.word at hBword; omega
  have hPliteral : (p : ℤ) ≤ lim.word := by unfold LightWeightedGlobalDigitLength.word at hPword; omega
  have hRword := hbudget (r M n) (by unfold word; omega)
  have hJword := hbudget (J M b n U) (by unfold word; omega)
  have hDword := hbudget (dim M b p K n U) (by unfold word; omega)
  have hQword := hbudget (p ^ (dim M b p K n U)) (by unfold word; omega)
  have hn2Word := hbudget (n ^ 2) (by unfold word LightWeightedGlobalDigitLength.word; omega)
  have hnWord : (n : ℤ) ≤ lim.word := by
    have hh : n ≤ n ^ 2 := by nlinarith
    exact (Int.ofNat_le.mpr hh).trans hn2Word
  have hn2Nonneg : 0 ≤ (n : ℤ) * (n : ℤ) := by positivity
  have hn2Int : (n : ℤ) * (n : ℤ) ≤ lim.word := by simpa only [pow_two, Nat.cast_mul] using hn2Word
  have htarget : 0 < 8 * (J M b n U + 3) * p ^ (4 * K) := by have hp := (Fact.out : p.Prime).pos; positivity
  have htargetWord :=
    hbudget (8 * (J M b n U + 3) * p ^ (4 * K)) (by unfold word LightWeightedGlobalDigitLength.word; omega)
  have hconstantWord : ((8 * p ^ (4 * K) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 8 * p ^ (4 * K) ≤ 8 * (J M b n U + 3) * p ^ (4 * K) :=
      Nat.mul_le_mul_right _ (by omega : 8 ≤ 8 * (J M b n U + 3))
    exact (Int.ofNat_le.mpr hh).trans htargetWord
  have hJ3Word := hbudget (J M b n U + 3) (by unfold word; omega)
  have hpow (i : ℕ) (hi : i ≤ dim M b p K n U) : ((p ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).one_lt; omega) hi)).trans hQword
  apply Meets.of_body (by rfl)
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
    refine _root_.Light.Ends.setToThen (n ^ 2 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pow_two,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [pow_two, LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time,
              LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_two,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> omega)
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightWeightedGlobalDigitLength.clog_meets (P := program M b p K) (p := 1) (d := depth + 1) rfl μ hM
              (by positivity : 0 < n ^ 2) hMword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightWeightedGlobalDigitLength.clog_meets (P := program M b p K) (p := 1) (d := depth + 1) rfl μ hM
            (by positivity : 0 < n ^ 2) hMword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedGlobalDigitLength.clogTime,
            LightWeightedGlobalDigitLength.time, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedGlobalDigitLength.clogTime,
            LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro rr ν ⟨hr, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
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
          ((LightWeightedGlobalDigitLength.meets (P := program M b p K) (pMain := 2) (pClog := 1) (d := depth + 1) rfl
              rfl μ hb (by omega) hBword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightWeightedGlobalDigitLength.meets (P := program M b p K) (pMain := 2) (pClog := 1) (d := depth + 1) rfl
            rfl μ hb (by omega) hBword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, r, hr,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [r, hr, LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time,
              LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, r, hr, LightWeightedGlobalDigitLength.clogTime,
            LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro jj ν ⟨hj, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  have htInt : ((8 * p ^ (4 * K) : ℕ) : ℤ) * ((J M b n U : ℤ) + 3) ≤ lim.word := by
    convert htargetWord using 1 <;> push_cast <;> ring
  push_cast at hconstantWord htInt
  have hconstantNonneg : 0 ≤ (8 : ℤ) * (p : ℤ) ^ (4 * K) := by positivity
  have htNonneg : 0 ≤ (8 : ℤ) * (p : ℤ) ^ (4 * K) * ((J M b n U : ℤ) + 3) := by positivity
  dsimp only [J, r] at htInt htNonneg hJ3Word
  have htAlias :
    (8 : ℤ) * (p : ℤ) ^ (4 * K) * ((paddedLength b U (Nat.clog M (n ^ 2)) : ℤ) + 3) =
      8 * ((paddedLength b U (Nat.clog M (n ^ 2)) : ℤ) + 3) * (p : ℤ) ^ (4 * K) :=
    by ring
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (8 * (J M b n U + 3) * p ^ (4 * K) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, J, hj, r, hr,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [J, hj, r, hr, LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time,
              LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, J, hj, r, hr,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> omega)
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightWeightedGlobalDigitLength.clog_meets (P := program M b p K) (p := 1) (d := depth + 1) rfl μ
              (Fact.out : p.Prime).one_lt htarget hPword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightWeightedGlobalDigitLength.clog_meets (P := program M b p K) (p := 1) (d := depth + 1) rfl μ
            (Fact.out : p.Prime).one_lt htarget hPword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedGlobalDigitLength.clogTime,
            LightWeightedGlobalDigitLength.time, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedGlobalDigitLength.clogTime,
            LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro dd ν ⟨hd, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
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
          ((LightNatPower.meets (P := program M b p K) (p := 3) (d := depth + 1) rfl μ hDword hpow) _ (by omega)) ?_ ?_
          ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightNatPower.meets (P := program M b p K) (p := 3) (d := depth + 1) rfl μ hDword hpow) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dim, menuDegree, hd,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [dim, menuDegree, hd, LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time,
              LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dim, menuDegree, hd,
            LightWeightedGlobalDigitLength.clogTime, LightWeightedGlobalDigitLength.time, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro qq ν ⟨hq, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen dst (r M n) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, r, hr, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [r, hr, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, r, hr, LightNatPower.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (dst + 1) (J M b n U) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, J, hj, r, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [J, hj, r, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, J, hj, r, LightNatPower.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (dst + 2) (dim M b p K n U) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dim, menuDegree, hd, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [dim, menuDegree, hd, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dim, menuDegree, hd, LightNatPower.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (dst + 3) (p ^ (dim M b p K n U)) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hq, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hq, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hq, LightNatPower.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (p ^ (dim M b p K n U) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hq, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hq, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hq, LightNatPower.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    have hi4 : i < 4 := by simpa using hi
    interval_cases i <;> simp
  · ( try refine _root_.Light.SameOn.cell ?_
      intro x_p2m_9663818307484834615 hx_p2m_9663818307484834615
      first
      | ((  (repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3009151875232070344);
                  (try have := h_p2m_3009151875232070344 x_p2m_9663818307484834615 (by omega));
                  revert h_p2m_3009151875232070344))
            intros
            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
      |
        (simp [] at hx_p2m_9663818307484834615;
          ( (repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3647520905536426784);
                  (try have := h_p2m_3647520905536426784 x_p2m_9663818307484834615 (by omega));
                  revert h_p2m_3647520905536426784))
            intros
            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
      | ( ( (repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9109529018926690743);
                  (try have := h_p2m_9109529018926690743 x_p2m_9663818307484834615 (by omega));
                  revert h_p2m_9109529018926690743))
            intros
            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
          fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                      its condition K x does not follow from the hypotheses."))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
