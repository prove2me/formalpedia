-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:18:40.154218+00:00
-- url     : https://prove2.me/submissions/86720874-e183-4eb7-b6cd-13eaaa49531c

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_code_lt
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_meets
import Theorems.Thm_ThreeSum_LightTernaryCodes_zero_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_code_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_partialCost_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_code_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
theorem _root_.solution
    {pMain pDigit pZero pErase pRank pSearch N low high m powers bank nb bankVals near nn nearVals L T active bi ni d :
      ℕ}
    (hmain : P[pMain]? = some (body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (hrank : P[pRank]? = some (LightWeightedCost.body pDigit))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (bankCodes nearCodes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbankSpace : bank + nb ≤ lim.space) (hnearSpace : near + nn ≤ lim.space)
    (hbankVals : bankVals + nb ≤ lim.space) (hnearVals : nearVals + nn ≤ lim.space)
    (hspace : powers + (2 * N + 1) ≤ lim.space)
    (hword : ((nb + nn + 2 ^ (2 * N + 1) + 2740 * N + 3000 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((T + active + 16 : ℕ) : ℤ) ≤ lim.word) (hbankRead : ∀ j < nb, μ (bank + j) = (bankCodes j : ℤ))
    (hnearRead : ∀ j < nn, μ (near + j) = (nearCodes j : ℤ))
    (hbankSorted : ∀ j k, j < k → k < nb → bankCodes j < bankCodes k)
    (hnearSorted : ∀ j k, j < k → k < nn → nearCodes j < nearCodes k) (hpowers : Powers μ powers (2 * N))
    (hm : m < 2 ^ (2 * N)) (hlow : low ≤ 2 * N) (hhigh : high ≤ 2 * N) (hL : L ≤ 2 * N) (hnb : nb < 2 ^ L)
    (hnn : nn < 2 ^ L) (hnbpos : 0 < nb)
    (hbi : active ≠ 0 → digit N low high m ≠ 0 → predCost N low high m ≤ T → bi < nb ∧ bankCodes bi = code N low high m)
    (hni : active ≠ 0 → digit N low high m ≠ 0 → T < predCost N low high m → ni < nn ∧ nearCodes ni = code N low high m)
    (hd : d + 2 * N + 3 ≤ lim.depth) :
    Meets lim P pMain d [N, low, high, m, powers, bank, nb, bankVals, near, nn, nearVals, L, T, active] μ (time N L)
      (fun r ν => r = (key N low high m T active bankVals nearVals bi ni : ℤ) ∧ ν = μ) :=
  by
  have hpowWord : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word := by omega
  have hscalar : ((2740 * N + 3000 : ℕ) : ℤ) ≤ lim.word := by omega
  have htwoword : (2 : ℤ) ≤ lim.word := by omega
  have hcode := code_lt (low := low) (high := high) hm
  have hrankBound := LightWeightedCost.partialCost_le N (code N low high m) N
  have hpredWord : (code N low high m : ℤ) < lim.word :=
    by
    have hp : 2 ^ (2 * N) ≤ 2 ^ (2 * N + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Int.ofNat_lt.mpr hcode).trans_le ((Int.ofNat_le.mpr hp).trans hpowWord)
  have hdigitCall :=
    LightTernaryCodes.digit_meets (d := d + 1) hdigit herase μ hw hspace hpowWord hpowers hlow hhigh hm (by omega)
      htwoword
  have hzeroCall :=
    LightTernaryCodes.zero_meets (d := d + 1) hzero herase μ hw hspace hpowWord hpowers hlow hhigh hm (by omega)
  have honeCall :=
    LightMaskErase.meets herase μ hw hspace hpowWord hpowers (2 * N) high m le_rfl hhigh hm (d + 1) (by omega)
  have hrankCall :=
    LightWeightedCost.meets (d := d + 1) hrank hdigit herase μ hw hspace hpowWord hscalar hpowers hcode (by omega)
  apply Meets.of_body hmain
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
    | refine _root_.Light.Ends.callToThen (hdigitCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hdigitCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryCodes.digitTime,
            LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
              LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.digitTime,
            LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
    on_goal -1 => (rintro q ν ⟨hq, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  rcases hq with rfl
  refine
    Ends.pieceThen (T₁ := LightTernaryCodes.zeroTime (2 * N) + LightMaskErase.time (2 * N) + 100) (R := fun σ =>
      σ =
        ⟨frame
            [N, low, high, m, powers, bank, nb, bankVals, near, nn, nearVals, L, T, active, digit N low high m,
              code N low high m],
          μ⟩)
      ?lower ?tail (hT := by
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
            | (ring_nf; omega)))
  case lower =>
    unfold lowerBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen (digit N low high m = 1) (fun h1 => ?_) (fun hn1 => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit,
              LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
              LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [digit, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                LightWeightedCost.time, LightBandLookup.searchTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, LightTernaryCodes.digitTime,
              LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        first
        | refine _root_.Light.Ends.callToThen (hzeroCall _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hzeroCall ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                LightBandLookup.searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [digit, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                  LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, LightTernaryCodes.digitTime,
                LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
        on_goal -1 => (rintro z ν ⟨hz, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst ν
      rcases hz with rfl
      have h1' : LightTernaryCodes.digit (2 * N) low high m = 1 := h1
      simp [digit, code, h1', update_frame_setLocal]
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        first
        | refine _root_.Light.Ends.callToThen (honeCall _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen honeCall ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                LightBandLookup.searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [digit, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                  LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, LightTernaryCodes.digitTime,
                LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
        on_goal -1 => (rintro z ν ⟨hz, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst ν
      rcases hz with rfl
      have hn1' : LightTernaryCodes.digit (2 * N) low high m ≠ 1 := hn1
      simp [digit, code, hn1', LightTernaryCodes.oneCode, update_frame_setLocal]
  case tail =>
    rintro σ rfl
    unfold tailBody
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
      | refine _root_.Light.Ends.callToThen (hrankCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hrankCall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit, predCost,
              LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
              LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [digit, predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                LightWeightedCost.time, LightBandLookup.searchTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, predCost, LightTernaryCodes.digitTime,
              LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
      on_goal -1 => (rintro rk ν ⟨hrk, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    rcases hrk with rfl
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen (active = 0) (fun ha => ?_) (fun hna => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit, predCost,
              LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
              LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [digit, predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                LightWeightedCost.time, LightBandLookup.searchTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, predCost, LightTernaryCodes.digitTime,
              LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen bankVals ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                LightBandLookup.searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                  LightBandLookup.searchTime] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.digitTime,
                LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [key, ha], rfl⟩
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.iteIffThen (digit N low high m = 0) (fun hq => ?_) (fun hnq => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit, predCost,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                LightBandLookup.searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [digit, predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                  LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, predCost,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                LightBandLookup.searchTime] <;> omega)
        all_goals
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.setToThen bankVals ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                  LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                  LightBandLookup.searchTime]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.digitTime,
                  LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                  LightBandLookup.searchTime] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [key, hq], rfl⟩
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.iteIffThen (predCost N low high m ≤ T) (fun hb => ?_) (fun hnb' => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, digit, predCost,
                  LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                  LightBandLookup.searchTime]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [digit, predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, digit, predCost,
                  LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                  LightBandLookup.searchTime] <;> omega)
          all_goals
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_)
        · obtain ⟨hi, he⟩ := hbi hna hnq hb
          have hs :=
            LightTernaryLookup.code_meets (d := d + 1) hsearch μ (fun j => (bankCodes j : ℤ)) hw hbankSpace hspace
              (by omega) hbankRead hpowers (fun j k hj hk => Int.ofNat_lt.mpr (hbankSorted j k hj hk)) hi hL hnb
              (by omega)
          have haddr : (bankVals : ℤ) + ((bi + 1 : ℕ) : ℤ) - 1 = ((bankVals + bi : ℕ) : ℤ) := by omega
          have haddrWord : ((bankVals + bi : ℕ) : ℤ) ≤ lim.word :=
            by
            have hh : bankVals + bi ≤ lim.space := by omega
            exact (Int.ofNat_le.mpr hh).trans hw
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
            | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
            | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, he, digit,
                    predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [he, digit, predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime,
                      LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 => omega
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, he, digit, predCost,
                    LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
            on_goal -1 => (rintro ix ν ⟨hix, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
            refine _root_.Light.Ends.setToThen (bankVals + bi : ℕ) ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hix, haddr,
                    LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hix, haddr, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                      LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hix, haddr, LightTernaryCodes.digitTime,
                    LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                    LightBandLookup.searchTime] <;> omega)
            try with_unfolding_none refine _root_.Light.Ends.skip ?_
          exact ⟨by simp [key, hna, hnq, hb], rfl⟩
        · have hnt : T < predCost N low high m := by omega
          obtain ⟨hi, he⟩ := hni hna hnq hnt
          have hs :=
            LightTernaryLookup.code_meets (d := d + 1) hsearch μ (fun j => (nearCodes j : ℤ)) hw hnearSpace hspace
              (by omega) hnearRead hpowers (fun j k hj hk => Int.ofNat_lt.mpr (hnearSorted j k hj hk)) hi hL hnn
              (by omega)
          have haddr : (nearVals : ℤ) + ((ni + 1 : ℕ) : ℤ) - 1 = ((nearVals + ni : ℕ) : ℤ) := by omega
          have haddrWord : ((nearVals + ni : ℕ) : ℤ) ≤ lim.word :=
            by
            have hh : nearVals + ni ≤ lim.space := by omega
            exact (Int.ofNat_le.mpr hh).trans hw
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
            | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
            | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, he, digit,
                    predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [he, digit, predCost, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime,
                      LightMaskErase.time, LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 => omega
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, he, digit, predCost,
                    LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime] <;> omega)
            on_goal -1 => (rintro ix ν ⟨hix, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
            refine _root_.Light.Ends.setToThen (nearVals + ni : ℕ) ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hix, haddr,
                    LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                    LightWeightedCost.time, LightBandLookup.searchTime]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hix, haddr, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time,
                      LightWeightedCost.time, LightBandLookup.searchTime] <;> first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hix, haddr, LightTernaryCodes.digitTime,
                    LightTernaryCodes.zeroTime, LightMaskErase.time, LightWeightedCost.time,
                    LightBandLookup.searchTime] <;> omega)
            try with_unfolding_none refine _root_.Light.Ends.skip ?_
          exact ⟨by simp [key, hna, hnq, hnb'], rfl⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
