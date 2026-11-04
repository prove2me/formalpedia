-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalGlobalPreludeProof.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:01:00.431705+00:00
-- url     : https://prove2.me/submissions/12be7710-72e5-44ae-a68e-60cb9336aa12

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Theorems.Thm_Light_Ends_append
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
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightArgumentTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionBackendLayout_end_le
import Theorems.Thm_ThreeSum_LightExtensionBackend_program_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedMatrix_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightScales_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Theorems.Thm_ThreeSum_LightScales_program_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientMatrix_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
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
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_program_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_program_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalExtensionBackendSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_backendLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_dimensionsLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
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
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menuDegree_pos
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
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
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.backendLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.dimensionsLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
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
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits
noncomputable section
namespace ThreeSum.LightWeightedGlobalGlobalPreludeProof
open Light LightWeightedGlobalGlobalPrelude
open LightExtensionBackendLayout hiding params
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
private theorem dimensions_call {lim : Limits} {M b p K n U free depth : ℕ} [Fact p.Prime] (μ : ℕ → ℤ) (hM : 1 < M)
    (hb : 1 < b) (hn : 0 < n) (hw : (lim.space : ℤ) ≤ lim.word) (hs : dimensions free + 4 ≤ lim.space)
    (hd : depth + 1 < lim.depth) (hword : (LightWeightedGlobalDimensions.word M b p K n U : ℤ) ≤ lim.word) (κ : ℕ) :
    Meets lim (program M b p K κ) 5 depth [n, U, dimensions free] μ (LightWeightedGlobalDimensions.time M b p K n U)
      (fun z ν =>
        z = ((p ^ (LightWeightedGlobalDimensions.dim M b p K n U) : ℕ) : ℤ) ∧
          Seg ν (dimensions free)
              [(LightWeightedGlobalDimensions.r M n : ℤ), LightWeightedGlobalDimensions.J M b n U,
                LightWeightedGlobalDimensions.dim M b p K n U,
                (p ^ (LightWeightedGlobalDimensions.dim M b p K n U) : ℕ)] ∧
            Kept μ ν (dimensions free)) :=
  by
  have hh :=
    ReportingHostRelocation.meets (LightWeightedGlobalDimensions.program_meets μ hM hb hn hw hs hd hword)
      LightScales.program
  have hh' :=
    hh.append
      (LightWeightedGlobalExtensionBackendSetup.program.map (ReportingHostRelocation.relocate 9) ++
          LightNatPower.program.map (ReportingHostRelocation.relocate 48) ++
        [body M b p K κ])
  change
    Meets lim
      (dimensionsLibrary M b p K ++
        (LightWeightedGlobalExtensionBackendSetup.program.map (ReportingHostRelocation.relocate 9) ++
            LightNatPower.program.map (ReportingHostRelocation.relocate 48) ++
          [body M b p K κ]))
      5 depth _ _ _ _ at hh'
  convert hh' using 1
  unfold program libraries ReportingHostRelocation.program
  rw [backendLibrary_length]
  unfold backendLibrary ReportingHostRelocation.program
  rw [dimensionsLibrary_length]
  simp only [List.append_assoc]
private theorem backend_call {lim : Limits} {M b p K d q J free depth : ℕ} [Fact p.Prime] (μ : ℕ → ℤ) (hdim : 0 < d)
    (hq : p ^ d = q) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 14 < lim.depth)
    (hs : backend free + reserve d p q J ≤ lim.space) (κ : ℕ) :
    Meets lim (program M b p K κ) 47 depth [p, d, q, J, backend free] μ
      (LightWeightedGlobalExtensionBackendSetup.time (backend free) d p q J)
      (fun z ν =>
        ∃ c < q,
          z = ((c + 1 : ℕ) : ℤ) ∧
            Irreducible (TernaryExtensionEncoding.monicOfCode (p := p) d c) ∧
              (∀ s < q * q,
                  ∀ i < J + 2,
                    ν (physical (backend free) d q J + s * (J + 2) + i) =
                      (LightExtensionSeedMatrix.value
                          (TernaryExtensionEncoding.encodedMul
                            (LightExtensionBackend.modulusMonic (factor (backend free) d p q J) c))
                          q p s (TernarySignedLayout.offset J i) :
                        ℤ)) ∧
                Kept μ ν (backend free)) :=
  by
  have hh :=
    ReportingHostRelocation.meets (LightWeightedGlobalExtensionBackendSetup.program_meets μ hdim hq hw hd hs)
      (dimensionsLibrary M b p K)
  have hh' := hh.append (LightNatPower.program.map (ReportingHostRelocation.relocate 48) ++ [body M b p K κ])
  change
    Meets lim
      (backendLibrary M b p K ++ (LightNatPower.program.map (ReportingHostRelocation.relocate 48) ++ [body M b p K κ]))
      47 depth _ _ _ _ at hh'
  convert hh' using 1
  unfold program libraries ReportingHostRelocation.program
  rw [backendLibrary_length]
  simp only [List.append_assoc]
end ThreeSum.LightWeightedGlobalGlobalPreludeProof
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalGlobalPreludeProof
open Light LightWeightedGlobalGlobalPrelude
open LightExtensionBackendLayout hiding params
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalGlobalPreludeProof
theorem _root_.solution {lim : Limits} {M b p K κ n free depth : ℕ} [Fact p.Prime] (μ : ℕ → ℤ) (hM : 1 < M) (hb : 1 < b)
    (hn : 0 < n) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace :
      finish free (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ)) p
          (p ^ (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ))) (LightWeightedGlobalDimensions.J M b n (n ^ κ)) ≤
        lim.space)
    (hdepth : depth + 15 < lim.depth) (hScales : ((1000 * (n + 1) : ℕ) : ℤ) ≤ lim.word)
    (hDimensions : (LightWeightedGlobalDimensions.word M b p K n (n ^ κ) : ℤ) ≤ lim.word)
    (hU : ((n ^ κ : ℕ) : ℤ) ≤ lim.word) (hκ : (κ : ℤ) ≤ lim.word) :
    Meets lim (program M b p K κ) 49 depth [n, free] μ (time M b p K κ n free)
      (fun z ν =>
        ∃ c < p ^ (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ)),
          z = (free : ℤ) ∧
            Irreducible
                (TernaryExtensionEncoding.monicOfCode (p := p) (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ))
                  c) ∧
              Seg ν free
                  (header n (n ^ κ) (LightWeightedGlobalDimensions.r M n)
                    (LightWeightedGlobalDimensions.J M b n (n ^ κ))
                    (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ)) p
                    (p ^ (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ))) free c) ∧
                Seg ν (params free) (LightScales.values n) ∧
                  Menu ν (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ)) p
                      (p ^ (LightWeightedGlobalDimensions.dim M b p K n (n ^ κ)))
                      (LightWeightedGlobalDimensions.J M b n (n ^ κ)) c ∧
                    Kept μ ν free) :=
  by
  let U := n ^ κ
  let R := LightWeightedGlobalDimensions.r M n
  let J := LightWeightedGlobalDimensions.J M b n U
  let D := LightWeightedGlobalDimensions.dim M b p K n U
  let Q := p ^ D
  let B := D + p + Q + J + 2
  have hDpos : 0 < D := TernaryExtensionEncoding.menuDegree_pos (p := p) _ _
  have hBpos : 1 ≤ B := by dsimp [B]; omega
  have hres : reserve D p Q J ≤ lim.space := by change backend free + reserve D p Q J ≤ lim.space at hspace; omega
  have hEnd : backend free + reserve D p Q J ≤ lim.space := hspace
  have hB6 : B ^ 6 ≤ reserve D p Q J := by change B ^ 6 ≤ 100000000 * B ^ 6; omega
  have hB1 : B ≤ B ^ 6 := by simpa only [pow_one] using Nat.pow_le_pow_right hBpos (show 1 ≤ 6 by decide)
  have hBword : (B : ℤ) ≤ lim.word := (Int.ofNat_le.mpr ((hB1.trans hB6).trans hres)).trans hw
  have hB6word : ((B ^ 6 : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hB6.trans hres)).trans hw
  have hcoeff : 100000000 ≤ reserve D p Q J :=
    by
    have hh := Nat.one_le_pow 6 B hBpos
    change 100000000 ≤ 100000000 * B ^ 6
    nlinarith
  have hcoeffWord : (100000000 : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hcoeff.trans hres)).trans hw
  have hBase : backend free ≤ lim.space := by omega
  have hfreeEnd : free + 33 ≤ lim.space := by simpa only [backend] using hBase
  have hpWord : (p : ℤ) ≤ lim.word := by dsimp [B] at hBword; omega
  have h6 : (6 : ℤ) ≤ lim.word := by omega
  have hPower (i : ℕ) (hi : i ≤ κ) : ((n ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hn hi)).trans hU
  have hFinalPower (i : ℕ) (hi : i ≤ 6) : ((B ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hBpos hi)).trans hB6word
  have hpowers : (program M b p K κ)[48]? = some LightNatPower.body :=
    by
    unfold program
    rw [List.getElem?_append_left (by simp)]
    unfold libraries ReportingHostRelocation.program
    rw [List.getElem?_append_right (by simp)]
    simp [backendLibrary_length, LightNatPower.program, LightNatPower.body]
  have hSc : LightScales.Procs (program M b p K κ) 0 := by constructor <;> rfl
  have hscSpace : params free + 5 ≤ lim.space := by unfold params; omega
  have hdimSpace : dimensions free + 4 ≤ lim.space := by unfold dimensions; omega
  have hPow := LightNatPower.meets (d := depth + 1) hpowers μ hκ hPower
  have hPhysicalEnd : physical (backend free) D Q J ≤ lim.space :=
    by
    have hh := LightExtensionBackendLayout.end_le (backend free) D p Q J
    have hb : physical (backend free) D Q J ≤ sum (backend free) D Q J + 2 * D := by
      unfold sum prod LightExtensionBackendLayout.r h LightExtensionBackendLayout.b a; omega
    exact hb.trans (hh.trans hEnd)
  have hPhysicalCalc :
    (backend free : ℤ) + 4 * (D : ℤ) + 11 + (Q : ℤ) * (Q : ℤ) + (Q : ℤ) * (Q : ℤ) * ((J : ℤ) + 2) ≤ lim.word :=
    by
    have hh : (physical (backend free) D Q J : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hPhysicalEnd).trans hw
    simp only [physical, logical, table, ctx, target, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hh
    convert hh using 1 <;> ring
  have hQQ : ((Q * Q : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : Q * Q ≤ physical (backend free) D Q J := by unfold physical logical; omega
    exact (Int.ofNat_le.mpr (hh.trans hPhysicalEnd)).trans hw
  have hlen : ((J + 2 : ℕ) : ℤ) ≤ lim.word := by dsimp [B] at hBword; omega
  have hpartial : (backend free : ℤ) + 4 * (D : ℤ) + 11 + (Q : ℤ) * (Q : ℤ) ≤ lim.word :=
    by
    have hz : 0 ≤ (Q : ℤ) * (Q : ℤ) * ((J : ℤ) + 2) := by positivity
    omega
  have hproduct : (Q : ℤ) * (Q : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by omega
  have hQ0 : (0 : ℤ) ≤ (p : ℤ) ^ D := by positivity
  have hQQ0 : (0 : ℤ) ≤ (Q : ℤ) * (Q : ℤ) := by positivity
  have hprod0 : (0 : ℤ) ≤ (Q : ℤ) * (Q : ℤ) * ((J : ℤ) + 2) := by positivity
  have hreserveCalc : (backend free : ℤ) + 100000000 * (B : ℤ) ^ 6 ≤ lim.word :=
    by
    have hh : (backend free + reserve D p Q J : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hEnd).trans hw
    change (backend free + 100000000 * B ^ 6 : ℤ) ≤ lim.word at hh
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hh
  have hReserveProd : (100000000 : ℤ) * (B : ℤ) ^ 6 ≤ lim.word := by omega
  have hReserve0 : (0 : ℤ) ≤ 100000000 * (B : ℤ) ^ 6 := by positivity
  simp only [U, R, J, D, Q, B, backend, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_ofNat] at hQ0 hQQ hQQ0 hlen hPhysicalCalc hpartial hproduct hprod0 hBword hReserveProd hReserve0 hreserveCalc
  apply
    Meets.of_body
      (show (program M b p K κ)[49]? = some (body M b p K κ) from
        by
        unfold program
        rw [List.getElem?_append_right (by simp)]
        simp only [libraries_length, Nat.sub_self, List.getElem?_cons_zero])
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
    | refine _root_.Light.Ends.callToThen (hPow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hPow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U] <;> omega)
    on_goal -1 => (rintro magnitude μp ⟨hMagnitude, hμp⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μp
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (params free : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, params]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [params] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, params] <;> omega)
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
    refine _root_.Light.Ends.setToThen (dimensions free : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, params, dimensions]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [params, dimensions] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, params, dimensions] <;> omega)
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
    refine _root_.Light.Ends.setToThen (backend free : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend] <;> omega)
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
        _root_.Light.Ends.callToThen ((hSc.meets (d := depth + 1) (μ := μ) hw hscSpace hScales (by omega)) _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (hSc.meets (d := depth + 1) (μ := μ) hw hscSpace hScales (by omega)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend] <;> omega)
    on_goal -1 =>
      (rintro scales μs ⟨hScalesResult, hScalesSeg, hScalesKeep⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hDim' := dimensions_call (depth := depth + 1) μs hM hb hn hw hdimSpace (by omega) hDimensions κ
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
    | refine _root_.Light.Ends.callToThen (hDim' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hDim' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            U, hMagnitude]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, U, hMagnitude] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, U,
            hMagnitude] <;> omega)
    on_goal -1 =>
      (rintro dims μd ⟨hDimResult, hDimSeg, hDimKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hread (i : ℕ) (hi : i < 4) := hDimSeg i (by simpa using hi)
  have ha0 : ((dimensions free : ℤ)).toNat = dimensions free := by omega
  have ha1 : ((dimensions free : ℤ) + 1).toNat = dimensions free + 1 := by omega
  have ha2 : ((dimensions free : ℤ) + 2).toNat = dimensions free + 2 := by omega
  have ha3 : ((dimensions free : ℤ) + 3).toNat = dimensions free + 3 := by omega
  have hr : μd (dimensions free) = (R : ℤ) := by simpa [R] using hread 0 (by decide)
  have hj : μd (dimensions free + 1) = (J : ℤ) := by simpa [J, U] using hread 1 (by decide)
  have hd : μd (dimensions free + 2) = (D : ℤ) := by simpa [D, U] using hread 2 (by decide)
  have hq : μd (dimensions free + 3) = (Q : ℤ) := by simpa [Q, D, U] using hread 3 (by decide)
  have hf29 : ((free : ℤ) + 29).toNat = free + 29 := by omega
  have hf30 : ((free : ℤ) + 30).toNat = free + 30 := by omega
  have hf31 : ((free : ℤ) + 31).toNat = free + 31 := by omega
  have hf32 : ((free : ℤ) + 32).toNat = free + 32 := by omega
  have hf291 : ((free : ℤ) + 29 + 1).toNat = free + 30 := by omega
  have hf292 : ((free : ℤ) + 29 + 2).toNat = free + 31 := by omega
  have hf293 : ((free : ℤ) + 29 + 3).toNat = free + 32 := by omega
  simp only [dimensions, Nat.add_assoc, Nat.reduceAdd] at hr hj hd hq
  have hRWord : (R : ℤ) ≤ lim.word := by dsimp [R]; unfold LightWeightedGlobalDimensions.word at hDimensions; omega
  have hJWord : (J : ℤ) ≤ lim.word := by dsimp only [J, U]; omega
  have hDWord : (D : ℤ) ≤ lim.word := by dsimp only [D, U]; omega
  have hQWord : (Q : ℤ) ≤ lim.word := by dsimp only [Q, D, U]; push_cast; omega
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen R ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hr, ha0, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hr, ha0, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hr,
            ha0, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.setToThen J ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hj, ha1, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hj, ha1, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hj,
            ha1, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.setToThen D ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hd, ha2, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hd, ha2, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hd,
            ha2, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.setToThen Q ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hq, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hq, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hq,
            ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
          ((backend_call (depth := depth + 1) μd hDpos rfl hw (by omega) hEnd κ) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (backend_call (depth := depth + 1) μd hDpos rfl hw (by omega) hEnd κ) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32,
              hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hr,
            hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
    on_goal -1 =>
      (rintro irreducible μb ⟨c, hc, hIrredResult, hIrred, hMenu, hBackendKeep⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (Q * Q : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32,
              hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hr,
            hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.setToThen (J + 2 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32,
              hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hr,
            hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.setToThen (physical (backend free) D Q J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            physical, logical, table, ctx, target, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291,
            hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, physical, logical, table, ctx, target, hr, hj, hd, hq, ha0,
              ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend,
            physical, logical, table, ctx, target, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291,
            hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.setToThen B ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, B, params, dimensions,
            backend, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, B, params, dimensions, backend, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31,
              hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, B, params, dimensions, backend,
            hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
        _root_.Light.Ends.callToThen ((LightNatPower.meets (d := depth + 1) hpowers μb h6 hFinalPower) _ (by omega)) ?_
          ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightNatPower.meets (d := depth + 1) hpowers μb h6 hFinalPower) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, B, params, dimensions,
            backend]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, B, params, dimensions, backend] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, B, params, dimensions,
            backend] <;> omega)
    on_goal -1 =>
      (rintro finalPower μb' ⟨hFinalPowerResult, hμb'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μb'
  simp only [U, J, D, Q, B, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hFinalPowerResult
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (finish free D p Q J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, finish, reserve,
            LightExtensionBackendLayout.params, B, params, dimensions, backend, hFinalPowerResult, hr, hj, hd, hq, ha0,
            ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, finish, reserve, LightExtensionBackendLayout.params, B, params, dimensions, backend,
              hFinalPowerResult, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, finish, reserve,
            LightExtensionBackendLayout.params, B, params, dimensions, backend, hFinalPowerResult, hr, hj, hd, hq, ha0,
            ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen free n ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 1) U ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            U, hMagnitude]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, U, hMagnitude] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, U,
            hMagnitude] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 2) R ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hr, ha0, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hr, ha0, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hr,
            ha0, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 3) J ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hj, ha1, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hj, ha1, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hj,
            ha1, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 4) D ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hd, ha2, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hd, ha2, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hd,
            ha2, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 5) Q ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hq, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hq, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend, hq,
            ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 6) (params free) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 7) (physical (backend free) D Q J) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            physical, logical, table, ctx, target, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291,
            hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, physical, logical, table, ctx, target, hr, hj, hd, hq, ha0,
              ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend,
            physical, logical, table, ctx, target, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291,
            hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 8) (finish free D p Q J) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            finish, reserve, LightExtensionBackendLayout.params, B, hFinalPowerResult, hr, hj, hd, hq, ha0, ha1, ha2,
            ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, finish, reserve, LightExtensionBackendLayout.params, B,
              hFinalPowerResult, hr, hj, hd, hq, ha0, ha1, ha2, ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend,
            finish, reserve, LightExtensionBackendLayout.params, B, hFinalPowerResult, hr, hj, hd, hq, ha0, ha1, ha2,
            ha3, hf29, hf30, hf31, hf32, hf291, hf292, hf293] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 9) (c + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend,
            hIrredResult]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend, hIrredResult] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend,
            hIrredResult] <;> omega)
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
    refine _root_.Light.Ends.setToThen free ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, U, R, J, D, Q, params, dimensions, backend]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [U, R, J, D, Q, params, dimensions, backend] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, U, R, J, D, Q, params, dimensions, backend] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨c, hc, rfl, hIrred, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi10 : i < 10 := by simpa [header] using hi
    interval_cases i <;> simp [header, U, R, J, D, Q, params, finish]
  · intro i hi
    have hi5 : i < 5 := by simpa [LightScales.values] using hi
    simp only [params] at *
    simp only [Function.update_of_ne (by omega : free + 10 + i ≠ free + 9),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 8),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 7),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 6),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 5),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 4),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 3),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 2),
      Function.update_of_ne (by omega : free + 10 + i ≠ free + 1),
      Function.update_of_ne (by omega : free + 10 + i ≠ free)]
    rw [hBackendKeep _ (by unfold backend; omega), hDimKeep _ (by unfold dimensions; omega)]
    exact hScalesSeg i hi
  · change Menu _ (backend free) D p Q J c
    intro seed hseed i hi
    have hsep : free + 10 ≤ physical (backend free) D Q J :=
      by
      unfold physical logical table ctx target backend
      omega
    simp only [Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 9),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 8),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 7),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 6),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 5),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 4),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 3),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 2),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free + 1),
      Function.update_of_ne (by omega : physical (backend free) D Q J + seed * (J + 2) + i ≠ free)]
    exact hMenu seed hseed i hi
  · intro x hx
    simp only [Function.update_of_ne (by omega : x ≠ free + 9), Function.update_of_ne (by omega : x ≠ free + 8),
      Function.update_of_ne (by omega : x ≠ free + 7), Function.update_of_ne (by omega : x ≠ free + 6),
      Function.update_of_ne (by omega : x ≠ free + 5), Function.update_of_ne (by omega : x ≠ free + 4),
      Function.update_of_ne (by omega : x ≠ free + 3), Function.update_of_ne (by omega : x ≠ free + 2),
      Function.update_of_ne (by omega : x ≠ free + 1), Function.update_of_ne (by omega : x ≠ free)]
    rw [hBackendKeep x (by unfold backend; omega), hDimKeep x (by unfold dimensions; omega),
      hScalesKeep x (Or.inl (by unfold params; omega))]
end ThreeSum.LightWeightedGlobalGlobalPreludeProof
