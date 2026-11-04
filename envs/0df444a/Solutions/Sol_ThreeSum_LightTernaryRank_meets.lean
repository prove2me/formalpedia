-- Prove2me | solution 1 for ThreeSum.LightTernaryRank.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:33.910525+00:00
-- url     : https://prove2.me/submissions/0df79814-94bc-4c03-a7dc-68a81bf57aa3

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_succ
import Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryRank
theorem _root_.solution {pMain pDigit pErase N m powers d : ℕ} (hmain : P[pMain]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (2 * N + 1) ≤ lim.space) (hword : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2 * N + 16 : ℕ) : ℤ) ≤ lim.word) (hpowers : Powers μ powers (2 * N)) (hm : m < 2 ^ (2 * N))
    (hdepth : d + 2 * N + 2 ≤ lim.depth) :
    Meets lim P pMain d [N, m, powers] μ (time N) (fun r ν => r = (partialRank N m N : ℤ) ∧ ν = μ) :=
  by
  have hnword : (N : ℤ) ≤ lim.word := by omega
  have htwoword : (2 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body hmain
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
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
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := N * (LightTernaryCodes.digitTime (2 * N) + 140) + 20) (Q := Inv N m powers μ N) (Inv N m powers μ)
        N (LightTernaryCodes.digitTime (2 * N) + 120) ?_ ?_ ?_ ?_ (hT := by
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
              | (ring_nf; omega))))
      ?_
  · refine ⟨0, 0, ?_⟩
    simp only [partialRank, sum_range_zero, update_frame_setLocal]
    change
      State.mk (frame [(N : ℤ), m, powers, 0, 0]) μ =
        State.mk (frame ([(N : ℤ), m, powers, 0, 0] ++ List.replicate 2 0)) μ
    exact congrArg (fun loc => State.mk loc μ) (frame_append_zeros [(N : ℤ), m, powers, 0, 0] 2).symm
  · rintro j _ hj _ ⟨lo, res, rfl⟩
    let lowJ := 2 * (N - 1 - j)
    have hlo : lowJ < 2 * N := by dsimp [lowJ]; omega
    have hhi : lowJ + 1 < 2 * N := by dsimp [lowJ]; omega
    have hlowWord : (lowJ : ℤ) ≤ lim.word := by omega
    have hhighWord : ((lowJ + 1 : ℕ) : ℤ) ≤ lim.word := by omega
    have hcast : 2 * ((N : ℤ) - 1 - (j : ℤ)) = (lowJ : ℤ) := by dsimp [lowJ]; omega
    have hcall :=
      LightTernaryCodes.digit_meets (d := d + 1) hdigit herase μ hw hspace hword hpowers (Nat.le_of_lt hlo)
        (Nat.le_of_lt hhi) hm (by omega) htwoword
    have hsum := partialRank_le N m (j + 1)
    have hsumWord : ((partialRank N m (j + 1) : ℕ) : ℤ) ≤ lim.word := by omega
    have hsumCast : (partialRank N m j : ℤ) + (digitAt N m j : ℤ) = (partialRank N m (j + 1) : ℤ) := by
      rw [partialRank_succ, Nat.cast_add]
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
      refine _root_.Light.Ends.setToThen lowJ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcast]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcast] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcast] <;> omega)
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcast,
              LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcast, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcast, LightTernaryCodes.digitTime] <;> omega)
      on_goal -1 => (rintro result ν ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    have hres : result = (digitAt N m j : ℤ) := by simpa [digitAt, lowJ] using hr
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (partialRank N m (j + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres, hsumCast]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hres, hsumCast] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres, hsumCast] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    constructor
    · simp [update_frame_setLocal]
    · refine ⟨lowJ, result, ?_⟩
      simp [Inv, update_frame_setLocal, Nat.cast_add]
  · intro σ hc hI
    exact hI
  · rintro j _ hj _ ⟨lo, res, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · rintro σ ⟨lo, res, rfl⟩
    have hsum := partialRank_le N m N
    have hsumWord : (partialRank N m N : ℤ) ≤ lim.word := by omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (partialRank N m N : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl, rfl⟩
end ThreeSum.LightTernaryRank
