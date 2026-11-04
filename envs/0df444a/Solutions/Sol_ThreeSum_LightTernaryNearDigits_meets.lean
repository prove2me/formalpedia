-- Prove2me | solution 1 for ThreeSum.LightTernaryNearDigits.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:41.286588+00:00
-- url     : https://prove2.me/submissions/fd7fac42-8a65-403a-b125-6e760b8d14ed

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_le_two
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_meets
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearDigits
theorem _root_.solution {pMain pDigit pErase N m powers caps active d : ℕ} (hmain : P[pMain]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (2 * N + 1) ≤ lim.space) (hword : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2 ^ (2 * N))
    (hcaps : caps + N ≤ active) (hactive : active + N ≤ powers) (hpowers : Powers μ powers (2 * N))
    (hd : d + 2 * N + 2 ≤ lim.depth) :
    Meets lim P pMain d [N, m, powers, caps, active] μ (time N)
      (fun _ ν =>
        (∀ i < N, ν (caps + i) = (LightTernaryRank.digitAt N m i : ℤ)) ∧
          (∀ i < N, ν (active + i) = 1) ∧ SameOutside μ ν caps (active + N - caps)) :=
  by
  have hcapLe : caps ≤ active + N := by omega
  have hspan : caps + (active + N - caps) = active + N := Nat.add_sub_of_le hcapLe
  have htwoword : (2 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ N m powers caps active) N (LightTernaryCodes.digitTime (2 * N) + 180) ?start ?round ?done ?bound
      (hT := by
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
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, 0, μ, ?_, SameOn.refl, ?_, ?_⟩
    · simp [update_frame_setLocal]
      change frame [(N : ℤ), m, powers, caps, active, 0] = frame ([(N : ℤ), m, powers, caps, active, 0] ++ [0, 0, 0])
      exact (frame_append_zeros _ 3).symm
    all_goals intro i hi; omega
  case round =>
    rintro j _ hj _ ⟨lo, hi, dig, ν, rfl, H, hcapsRead, hactiveRead⟩
    have hPowers : Powers ν powers (2 * N) := by
      intro i hi
      rw [H _ (Or.inr (by omega))]
      exact hpowers i hi
    have hl : 2 * (N - 1 - j) ≤ 2 * N := by omega
    have hh : 2 * (N - 1 - j) + 1 ≤ 2 * N := by omega
    have hlo : 2 * ((N : ℤ) - 1 - (j : ℤ)) = ((2 * (N - 1 - j) : ℕ) : ℤ) := by omega
    have hdigitBound := LightTernaryCodes.digit_le_two (2 * N) (2 * (N - 1 - j)) (2 * (N - 1 - j) + 1) m
    have hdigitEq :
      LightTernaryCodes.digit (2 * N) (2 * (N - 1 - j)) (2 * (N - 1 - j) + 1) m = LightTernaryRank.digitAt N m j := rfl
    have hc :=
      LightTernaryCodes.digit_meets (d := d + 1) hdigit herase ν hw hspace hword hPowers hl hh hm (by omega) htwoword
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (2 * (N - 1 - j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlo,
              LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hlo, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlo, LightTernaryCodes.digitTime] <;> omega)
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
      refine _root_.Light.Ends.setToThen (2 * (N - 1 - j) + 1 : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.digitTime] <;> omega)
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.digitTime] <;> omega)
      on_goal -1 => (rintro r ξ ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ξ
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (caps + j) (LightTernaryRank.digitAt N m j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, hdigitEq,
              LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, hdigitEq, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hdigitEq, LightTernaryCodes.digitTime] <;>
            omega)
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
      refine _root_.Light.Ends.storeToThen (active + j) (1 : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.digitTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, (2 * (N - 1 - j) : ℕ), (2 * (N - 1 - j) + 1 : ℕ), r,
        Function.update (Function.update ν (caps + j) (LightTernaryRank.digitAt N m j : ℤ)) (active + j) 1, ?_, ?_, ?_,
        ?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      simp only [Function.update_of_ne (by omega : x ≠ active + j), Function.update_of_ne (by omega : x ≠ caps + j)]
      exact H x hx
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | he
      · rw [Function.update_of_ne (by omega : caps + i ≠ active + j),
          Function.update_of_ne (by omega : caps + i ≠ caps + j)]
        exact hcapsRead i hi
      · subst i
        simp [Function.update_of_ne (by omega : caps + j ≠ active + j)]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | he
      · rw [Function.update_of_ne (by omega : active + i ≠ active + j),
          Function.update_of_ne (by omega : active + i ≠ caps + j)]
        exact hactiveRead i hi
      · subst i
        simp
  case done =>
    rintro _ _ ⟨lo, hi, dig, ν, rfl, H, hcapsRead, hactiveRead⟩
    exact ⟨hcapsRead, hactiveRead, H⟩
  case bound =>
    rintro j _ hj _ ⟨lo, hi, dig, ν, rfl, H, hcapsRead, hactiveRead⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightTernaryNearDigits
