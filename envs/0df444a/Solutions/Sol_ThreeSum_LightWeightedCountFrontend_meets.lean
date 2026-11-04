-- Prove2me | solution 1 for ThreeSum.LightWeightedCountFrontend.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:22:49.504792+00:00
-- url     : https://prove2.me/submissions/ceca709d-2afc-4aa4-82c9-4d7361b293a3

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_Weighted_GroupBankResources
import Definitions.Def_Submission_Weighted_WantedRows
import Definitions.Def_Submission_Weighted_CountFrontend
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_library
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
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
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Plan_snapshot
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_assembled_inverse_bank
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_source_bank_read
import Theorems.Thm_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
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
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
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
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.LightWeightedWantedRows.program_length
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
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
namespace ThreeSum.LightWeightedCountFrontend
theorem _root_.solution {lim : Limits}
    {N bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst d V t : ℕ} (f g : Config)
    (Qstar : TritWord N) (Q : ℕ → TritWord N) (group : ℕ → ℕ) (F G : ℕ → TritWord N → ℤ) (E : Enumeration N f.T f.nb)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : f.bank + f.nb ≤ keyBase)
    (hfs : fsource + groups * f.nb ≤ keyBase) (hgs : gsource + groups * f.nb ≤ keyBase)
    (hmeta : keyBase + 4 * f.nb ≤ bankPowers) (hpows : bankPowers + (2 * N + 1) ≤ fbase)
    (hfg : fbase + groups * ((N + 1) * f.nb) ≤ gbase) (hgh : gbase + groups * ((N + 1) * f.nb) ≤ hbase)
    (hHdst : hbase + groups * ((N + 1) * f.nb) ≤ dst) (hword : ((f.nb + 2 ^ (2 * N + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hNword : 2 * (N : ℤ) + 3 ≤ lim.word) (hgroupsWord : (groups : ℤ) + 1 ≤ lim.word)
    (hcodes : ∀ j < f.nb, μ (f.bank + j) = (address (E.word j) : ℤ))
    (hsourceF : ∀ g < groups, ∀ j < f.nb, μ (fsource + g * f.nb + j) = F g (E.word j))
    (hsourceG : ∀ g < groups, ∀ j < f.nb, μ (gsource + g * f.nb + j) = G g (E.word j))
    (hsorted : ∀ j k, j < k → k < f.nb → address (E.word j) < address (E.word k))
    (hF : ∀ g < groups, ∀ R, |F g R| ≤ (V : ℤ)) (hG : ∀ g < groups, ∀ R, |G g R| ≤ (V : ℤ))
    (hforwardWord : 4 * ((4 ^ N * V : ℕ) : ℤ) + 3 ≤ lim.word)
    (hproductWord : (LightWeightedBankAssembly.valueBound N V : ℤ) ≤ lim.word)
    (hinverseWord : 4 * ((4 ^ N * LightWeightedBankAssembly.valueBound N V : ℕ) : ℤ) + 3 ≤ lim.word) (hL : f.L ≤ 2 * N)
    (hn : f.nb < 2 ^ f.L) (hrecords : records + 3 * count ≤ keyBase) (hdst : dst + count ≤ f.a)
    (hspace : f.a ≤ lim.space) (hreadGroup : ∀ j < count, μ (records + 3 * j + 2) = (group j : ℤ))
    (hreadQ : ∀ j < count, μ (records + 3 * j + 1) = (address (Q j) : ℤ)) (hgroup : ∀ j < count, group j < groups)
    (hRank : ∀ j < count, cacheCost (Q j) = cacheCost Qstar) (hcountWord : (count : ℤ) + 1 ≤ lim.word)
    (hstrideWord : (((N + 1) * f.nb : ℕ) : ℤ) ≤ lim.word) (htailWord : ((N * f.nb : ℕ) : ℤ) ≤ lim.word)
    (hplan :
      ∀ j < count,
        Plan lim out (hbase + group j * ((N + 1) * f.nb)) caps
          (sourceConfig f fbase ((N + 1) * f.nb) (N * f.nb) (group j))
          (sourceConfig g gbase ((N + 1) * f.nb) (N * f.nb) (group j)) (Q j) E (F (group j)) (G (group j)))
    (htime :
      ∀ j < count,
        LightWeightedPreparedWanted.time (sourceConfig f fbase ((N + 1) * f.nb) (N * f.nb) (group j))
            (sourceConfig g gbase ((N + 1) * f.nb) (N * f.nb) (group j)) (Q j) ≤
          t)
    (hd : d + 3 * N + f.L + 16 ≤ lim.depth) :
    Meets lim program 63 d
      (args f g Qstar bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst) μ
      (time groups N f.L f.nb count t)
      (fun _ ν => Kept μ ν keyBase ∧ ∀ j < count, ν (dst + j) = LightWeightedWantedRows.score F G group Q j) :=
  by
  have hbankSpace : hbase + groups * ((N + 1) * f.nb) ≤ lim.space := by omega
  have hpowerSpace : bankPowers + (2 * N + 1) ≤ lim.space := by omega
  have hpowBound : ∀ j ≤ 2 * N + 1, ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    intro j hj
    have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hj
    have hcast : ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ (2 * N + 1) : ℕ) : ℤ) := by exact_mod_cast hle
    exact hcast.trans (by omega)
  have hpow :=
    powTable_meets (P := program) (p := 50) (d := d + 1) (μ := μ) (dst := bankPowers) (L := 2 * N + 1) (b := 2) rfl hw
      hpowerSpace hpowBound
  apply Meets.of_body main
  unfold body args time
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
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedWantedRows.args,
            LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedWantedRows.args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
              LightWeightedWantedQuery.args, LightWeightedNearPair.args, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedWantedRows.args,
            LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, powTableTime] <;> omega)
    on_goal -1 =>
      (rintro powerResult μp ⟨hpowSeg, hpowOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpowerPrefix : Kept μ μp keyBase := by
    intro x hx
    exact hpowOutside x (Or.inl (by omega))
  have hcodesP : ∀ j < f.nb, μp (f.bank + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    rw [hpowerPrefix _ (by omega)]
    exact hcodes j hj
  have hsourceFp : ∀ k < groups, ∀ j < f.nb, μp (fsource + k * f.nb + j) = F k (E.word j) :=
    by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb (show k + 1 ≤ groups by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    rw [hpowerPrefix _ (by omega)]
    exact hsourceF k hk j hj
  have hsourceGp : ∀ k < groups, ∀ j < f.nb, μp (gsource + k * f.nb + j) = G k (E.word j) :=
    by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb (show k + 1 ≤ groups by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    rw [hpowerPrefix _ (by omega)]
    exact hsourceG k hk j hj
  have hbank :=
    (LightWeightedGroupedBanks.meets (d := d + 1) E F G μp hw ha hfs hgs hmeta hpows hfg hgh hbankSpace hword hNword
          hgroupsWord hcodesP hsourceFp hsourceGp (powers_of_segment hpowSeg) hsorted hF hG hforwardWord hproductWord
          hinverseWord hL hn (by omega)).append
      tail
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
    | refine _root_.Light.Ends.callToThen (hbank _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hbank ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedWantedRows.args,
            LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, LightWeightedGroupedBanks.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedWantedRows.args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
              LightWeightedWantedQuery.args, LightWeightedNearPair.args, LightWeightedGroupedBanks.time,
              powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedWantedRows.args,
            LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, LightWeightedGroupedBanks.time, powTableTime] <;> omega)
    on_goal -1 =>
      (rintro bankResult ν ⟨hFst, hGst, hHst, hkeep, hpowers'⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hprefix : Kept μ ν keyBase := by
    intro x hx
    exact (hkeep x (Or.inl hx) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (hpowerPrefix x hx)
  have hcodes' : ∀ j < f.nb, ν (f.bank + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    rw [hprefix _ (by omega)]
    exact hcodes j hj
  have hsnapshot :
    ∀ j < count,
      Snapshot lim out (hbase + group j * ((N + 1) * f.nb)) caps
        (sourceConfig f fbase ((N + 1) * f.nb) (N * f.nb) (group j))
        (sourceConfig g gbase ((N + 1) * f.nb) (N * f.nb) (group j)) ν (Q j) E (F (group j)) (G (group j)) :=
    by
    intro j hj
    apply (hplan j hj).snapshot hcodes'
    · exact LightWeightedWantedQuery.source_bank_read E (F (group j)) ν (hFst (group j) (hgroup j hj))
    · exact LightWeightedWantedQuery.source_bank_read E (G (group j)) ν (hGst (group j) (hgroup j hj))
    ·
      exact
        LightWeightedWantedQuery.assembled_inverse_bank E (F (group j)) (G (group j)) ν (hHst (group j) (hgroup j hj))
  have hrowsGroup : ∀ j < count, ν (records + 3 * j + 2) = (group j : ℤ) :=
    by
    intro j hj
    rw [hprefix _ (by omega)]
    exact hreadGroup j hj
  have hrowsQ : ∀ j < count, ν (records + 3 * j + 1) = (address (Q j) : ℤ) :=
    by
    intro j hj
    rw [hprefix _ (by omega)]
    exact hreadQ j hj
  have hrows :=
    LightWeightedWantedRows.meets (P := program) (pMain := 62) (pRow := 61) (pPrepare := 60) (d := d + 1) (bankValues :=
      hbase) rows row prepared library f g Qstar Q group F G E ν hw (by omega) hdst hspace (by omega) hfg hgh hHdst
      (by ring) rfl hrowsGroup hrowsQ hgroup hRank (by omega) hcountWord hstrideWord htailWord hsnapshot htime
      (by omega)
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
    | refine _root_.Light.Ends.callToThen (hrows _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrows ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedWantedRows.args,
            LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, LightWeightedGroupedBanks.time, LightWeightedWantedRows.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedWantedRows.args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
              LightWeightedWantedQuery.args, LightWeightedNearPair.args, LightWeightedGroupedBanks.time,
              LightWeightedWantedRows.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedWantedRows.args,
            LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, LightWeightedGroupedBanks.time, LightWeightedWantedRows.time, powTableTime] <;> omega)
    on_goal -1 => (rintro result ξ ⟨hrowsKeep, hout⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, hout⟩
  intro x hx
  exact (hrowsKeep x (by omega)).trans (hprefix x hx)
end ThreeSum.LightWeightedCountFrontend
