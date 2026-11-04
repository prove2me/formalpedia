-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.step_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:23.313414+00:00
-- url     : https://prove2.me/submissions/9ee188f6-b9fa-4e76-8659-39207a93743c

import Definitions.Def_Submission_Weighted_FrozenBranches
import Definitions.Def_Submission_Weighted_FrozenPrepare
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
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
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
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
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
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
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution {pMain pSelf pLookup pDigit pZero pErase d branchTime : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (N K rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ) (q : Fin 3) (value : ℤ)
    (μ : ℕ → ℤ) (hK : K < N) (hbank : cut < rank) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (2 * N + 1) ≤ lim.space) (hword : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word)
    (hNword : 2 * (N : ℤ) + 3 ≤ lim.word) (hcutWord : (cut : ℤ) + 1 ≤ lim.word) (hpowers : Powers μ powers (2 * N))
    (hm : m < 2 ^ (2 * N))
    (hargs :
      ∀ x ∈ inputs N (K + 1) rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L,
        |x| ≤ lim.word)
    (hq : LightTernaryCodes.digit (2 * N) (2 * (N - (K + 1))) (2 * (N - (K + 1)) + 1) m = q.val)
    (hd : d + 2 * N + 2 ≤ lim.depth)
    (hbranch :
      Ends lim P d (branches pSelf)
        ⟨frame
            (preparedInputs N K rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L q
              (LightTernaryCodes.zeroCode (2 * N) (2 * (N - (K + 1))) (2 * (N - (K + 1)) + 1) m)
              (LightTernaryCodes.oneCode (2 * N) (2 * (N - (K + 1)) + 1) m)),
          μ⟩
        branchTime (fun σ => σ.loc 0 = value ∧ σ.mem = μ)) :
    Meets lim P pMain d
      (inputs N (K + 1) rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L) μ
      (prepTime N + branchTime) (fun v μ' => v = value ∧ μ' = μ) :=
  by
  have ha (x : ℤ)
    (hx : x ∈ inputs N (K + 1) rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L) :=
    abs_le.mp (hargs x hx)
  have hR := ha rank (by simp [inputs])
  have hT := ha cut (by simp [inputs])
  have hM := ha m (by simp [inputs])
  have hP := ha powers (by simp [inputs])
  have hkw := ha (K + 1) (by simp [inputs])
  have hsub : (N : ℤ) - ((K + 1 : ℕ) : ℤ) = ((N - (K + 1) : ℕ) : ℤ) := by omega
  have hlow : 2 * (N - (K + 1)) ≤ 2 * N := by omega
  have hhigh : 2 * (N - (K + 1)) + 1 ≤ 2 * N := by omega
  have hdi :=
    LightTernaryCodes.digit_meets (d := d + 1) hdigit herase μ hw hspace hword hpowers hlow hhigh hm (by omega)
      (by omega)
  have hze := LightTernaryCodes.zero_meets (d := d + 1) hzero herase μ hw hspace hword hpowers hlow hhigh hm (by omega)
  have her :=
    LightMaskErase.meets herase μ hw hspace hword hpowers (2 * N) (2 * (N - (K + 1)) + 1) m le_rfl hhigh hm (d + 1)
      (by omega)
  apply Meets.of_body hmain
  unfold body inputs prepTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.iteIffThen ((rank : ℤ) ≤ (cut : ℤ)) (fun he => ?_) (fun hn => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · exfalso; omega
  · focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen (((K + 1 : ℕ) : ℤ) = 0) (fun he => ?_) (fun hn => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · exfalso; omega
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (K : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;>
                first
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
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        first
        | refine _root_.Light.Ends.callToThen (hdi _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hdi ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hsub, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, LightTernaryCodes.digitTime,
                LightTernaryCodes.zeroTime, LightMaskErase.time] <;>
              omega)
        on_goal -1 => (rintro vd μd ⟨hvd, hmd⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst μd
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        first
        | refine _root_.Light.Ends.callToThen (hze _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hze ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hsub, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, LightTernaryCodes.digitTime,
                LightTernaryCodes.zeroTime, LightMaskErase.time] <;>
              omega)
        on_goal -1 => (rintro vz μz ⟨hvz, hmz⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst μz
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        first
        | refine _root_.Light.Ends.callToThen (her _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen her ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub,
                LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hsub, LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, LightTernaryCodes.digitTime,
                LightTernaryCodes.zeroTime, LightMaskErase.time] <;>
              omega)
        on_goal -1 => (rintro vo μo ⟨hvo, hmo⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst μo
      subst vd vz vo
      refine
        Ends.seq branchTime 0 ?_
          (by
            simp only [LightTernaryCodes.digitTime, LightTernaryCodes.zeroTime, LightMaskErase.time]
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [] <;>
                  first
                  | omega
                  | (ring_nf; omega)))
      simpa [branches, preparedInputs, inputs, LightTernaryCodes.oneCode, hq, setLocal] using
        (hbranch.mono le_rfl (fun σ hs => Ends.skip hs))
end ThreeSum.LightWeightedFrozenQuery
