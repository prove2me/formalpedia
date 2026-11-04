-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.row_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:29.145506+00:00
-- url     : https://prove2.me/submissions/e041bc8b-dd61-44c9-94fd-089d26c32770

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_5d4b5ec466dc091a
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution {pRow pDecode pDivide q J dst work V : ℕ} (hrow : P[pRow]? = some (rowBody pDecode))
    (hdecode : P[pDecode]? = some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 2 < lim.depth) (hq : q ≤ V) (hsep : dst + J + 1 ≤ work) (hspace : space work V ≤ lim.space)
    (hword : (word J V : ℤ) ≤ lim.word) :
    Meets lim P pRow d [q, J, dst, work] μ (rowTime J V)
      (fun r ν => r = (accepted J q : ℤ) ∧ Row ν dst J q ∧ Kept μ ν dst) :=
  by
  have hword' : (LightOutputDecodeDigits.word V 2 J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have h1Word : (1 : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold word; omega : 1 ≤ word J V)).trans hword
  have hwork : work ≤ lim.space := by unfold space LightOutputDecodeDigits.space at hspace; omega
  have hqWord : (q : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hq.trans (by unfold word LightOutputDecodeDigits.word; omega))).trans hword
  have hJWord : (J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : J ≤ word J V)).trans hword
  have h2Word : (2 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 2 ≤ word J V)).trans hword
  apply Meets.of_body hrow
  unfold rowBody rowTime
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightOutputDecodeDigits.meets (d := d + 1) (k := q) (J := J) (m := 2) (dst := dst + 1) (work := work) (V :=
              V) hdecode hdivide hw (by omega) (by decide) hq (by omega) hspace hword')
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightOutputDecodeDigits.meets (d := d + 1) (k := q) (J := J) (m := 2) (dst := dst + 1) (work := work) (V :=
            V) hdecode hdivide hw (by omega) (by decide) hq (by omega) hspace hword')
          ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro r ν ⟨hr, hbits, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen dst (0 : ℕ) ?_ ?_ ?_
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
  have hbits' : ∀ j < J, Function.update ν dst 0 (dst + J - j) = (digit 2 q j : ℤ) :=
    by
    intro j hj
    rw [Function.update_of_ne (by omega)]
    have he := hbits (J - 1 - j) (by omega)
    rw [OutputDecodeOrder.indices_getD_reverse 2 J q hj] at he
    have ha : dst + 1 + (J - 1 - j) = dst + J - j := by omega
    simpa only [ha, digit, quotient] using he
  have hread : Function.update ν dst 0 (dst + J) = (initial J q : ℤ) :=
    by
    by_cases hJ : J = 0
    · simp [hJ, initial]
    · simpa [initial, hJ] using hbits' 0 (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.iteIffThen ((initial J q : ℤ) = 0) (fun hy => ?_) (fun hn => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hread] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have he : initial J q = 0 := by exact_mod_cast hy
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
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
    refine ⟨by simp [accepted, he], ⟨by simp, hbits'⟩, ?_⟩
    intro a ha
    change Function.update ν dst 0 a = μ a
    rw [Function.update_of_ne (by omega), hkeep _ (by omega)]
  · have he : initial J q ≠ 0 := by exact_mod_cast hn
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
    refine ⟨by simp [accepted, he], ⟨by simp, hbits'⟩, ?_⟩
    intro a ha
    change Function.update ν dst 0 a = μ a
    rw [Function.update_of_ne (by omega), hkeep _ (by omega)]
end ThreeSum.LightTernaryCarryCodes
