-- Prove2me | solution 1 for ThreeSum.LightMaskBits.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:33:15.971606+00:00
-- url     : https://prove2.me/submissions/71136f6d-1d72-4b65-b13e-30824757ed01

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskBits
theorem _root_.solution {pMain pPowers pErase : ℕ} (hmain : P[pMain]? = some (body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody) (herase : P[pErase]? = some (LightMaskErase.body pErase)) {μ : ℕ → ℤ}
    {L m dst work : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 1 ≤ lim.depth)
    (hspace : work + (L + 1) ≤ lim.space) (hdst : dst + L ≤ work) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hm : m < 2 ^ L) :
    Meets lim P pMain d [L, m, dst, work] μ (time L)
      (fun _ μ' => (∀ j < L, μ' (dst + j) = (bit L m j : ℤ)) ∧ Powers μ' work L ∧ KeptBut μ μ' work dst L) :=
  by
  have hpL : ((2 ^ L : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (Nat.le_succ L))).trans hword
  have hmZ : (m : ℤ) < lim.word := (Int.ofNat_lt.mpr hm).trans_le hpL
  have htwo : (2 : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ 1 : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := L + 1) (b := 2) hpowers hw hspace
      (by
        intro j hj
        exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))).trans hword)
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
    on_goal -1 => (rintro r μ₁ ⟨hpow, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpow' : Powers μ₁ work L := powers_of_segment hpow
  unfold loopBody
  refine Ends.for (Inv μ L m dst work) L (LightMaskErase.time L + 72) ?_ ?_ ?_ ?_
  · refine ⟨r, μ₁, ?_, ?_, hpow', ?_⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
    · intro a ⟨ha, hout⟩; exact hkept a (Or.inl ha)
  · rintro j _ hj _ ⟨r, μ', rfl, written, pows, kept⟩
    have hc :=
      LightMaskErase.meets (W := L) (powers := work) herase μ' hw hspace hword pows L j m le_rfl (by omega) hm (d + 1)
        (by omega)
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
      on_goal -1 => (rintro v μ₂ ⟨hv, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((v : ℤ) = (m : ℤ)) (fun heZ => ?_) (fun hnZ => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have he : eraseMask L j m = m := by exact_mod_cast hv.symm.trans heZ
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen (dst + j) (0 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, v, Function.update μ' (dst + j) 0, by simp [update_frame_setLocal], ?_, ?_, ?_⟩
      · intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
        · rw [Function.update_of_ne (by omega)]
          exact written a ha
        · simp [bit, he]
      · intro a ha
        rw [Function.update_of_ne (by omega)]
        exact pows a ha
      · intro a ⟨ha, hout⟩
        rw [Function.update_of_ne (by omega)]
        exact kept a ⟨ha, hout⟩
    · have he : eraseMask L j m ≠ m := by
        intro hh
        apply hnZ
        simpa [hh] using hv
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen (dst + j) (1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, v, Function.update μ' (dst + j) 1, by simp [update_frame_setLocal], ?_, ?_, ?_⟩
      · intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
        · rw [Function.update_of_ne (by omega)]
          exact written a ha
        · simp [bit, he]
      · intro a ha
        rw [Function.update_of_ne (by omega)]
        exact pows a ha
      · intro a ⟨ha, hout⟩
        rw [Function.update_of_ne (by omega)]
        exact kept a ⟨ha, hout⟩
  · rintro _ _ ⟨r, μ', rfl, written, pows, kept⟩
    exact ⟨written, pows, kept⟩
  · rintro i _ _ _ ⟨r, μ', rfl, _, _, _⟩
    simp
end ThreeSum.LightMaskBits
