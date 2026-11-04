-- Prove2me | solution 1 for ThreeSum.LightColorIndex.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:56.829804+00:00
-- url     : https://prove2.me/submissions/7ca74486-2842-4f54-90e4-a9a34cde64a6

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Theorems.Thm_ThreeSum_LightColorIndex_erase_eq_iff_testBit_false
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
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
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightColorIndex
theorem _root_.solution {pMain pErase W m powers d : ℕ} (hmain : P[pMain]? = some (body pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers + (W + 1) ≤ lim.space)
    (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hpowers : Powers μ powers W) (hm : m < 2 ^ W)
    (hd : d + W + 1 ≤ lim.depth) :
    Meets lim P pMain d
      [W, m, p.1.1.val, p.1.2.val, (p.2 (false, false)).val, (p.2 (false, true)).val, (p.2 (true, false)).val,
        (p.2 (true, true)).val, powers]
      μ (time W) (fun r μ' => r = (color p m : ℤ) ∧ μ' = μ) :=
  by
  have ha := p.1.1.isLt
  have hb := p.1.2.isLt
  have h00 := (p.2 (false, false)).isLt
  have h01 := (p.2 (false, true)).isLt
  have h10 := (p.2 (true, false)).isLt
  have h11 := (p.2 (true, true)).isLt
  have htwo : (2 : ℤ) ≤ lim.word :=
    by
    have h2 : 2 ^ 1 ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast h2 : (2 : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hmWord : (m : ℤ) ≤ lim.word :=
    by
    have hpow : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Int.ofNat_le.mpr (by omega : m ≤ 2 ^ (W + 1))).trans hword
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightMaskErase.meets herase μ hw hspace hword hpowers W p.1.1.val m le_rfl (by omega) hm (d + 1) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightMaskErase.meets herase μ hw hspace hword hpowers W p.1.1.val m le_rfl (by omega) hm (d + 1) (by omega))
          ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro erasedA μ₁ ⟨hA, hmemA⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
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
          ((LightMaskErase.meets herase μ hw hspace hword hpowers W p.1.2.val m le_rfl (by omega) hm (d + 1) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightMaskErase.meets herase μ hw hspace hword hpowers W p.1.2.val m le_rfl (by omega) hm (d + 1) (by omega))
          ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro erasedB μ₂ ⟨hB, hmemB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
    refine _root_.Light.Ends.iteIffThen (erasedA = (m : ℤ)) (fun heA => ?_) (fun hnA => ?_) ?_ ?_
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
  · have hbitA := (erase_eq_iff_testBit_false hm p.1.1).mp (by exact_mod_cast hA.symm.trans heA)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen (erasedB = (m : ℤ)) (fun heB => ?_) (fun hnB => ?_) ?_ ?_
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
    · have hbitB := (erase_eq_iff_testBit_false hm p.1.2).mp (by exact_mod_cast hB.symm.trans heB)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen ((p.2 (false, false)).val : ℕ) ?_ ?_ ?_
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
      exact ⟨by simp [color, hbitA, hbitB], rfl⟩
    · have hbitB : m.testBit p.1.2.val = true :=
        by
        cases h : m.testBit p.1.2.val
        · have he := (erase_eq_iff_testBit_false hm p.1.2).mpr h
          exact False.elim (hnB (by simpa [he] using hB))
        · rfl
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen ((p.2 (false, true)).val : ℕ) ?_ ?_ ?_
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
      exact ⟨by simp [color, hbitA, hbitB], rfl⟩
  · have hbitA : m.testBit p.1.1.val = true := by
      cases h : m.testBit p.1.1.val
      · have he := (erase_eq_iff_testBit_false hm p.1.1).mpr h
        exact False.elim (hnA (by simpa [he] using hA))
      · rfl
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen (erasedB = (m : ℤ)) (fun heB => ?_) (fun hnB => ?_) ?_ ?_
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
    · have hbitB := (erase_eq_iff_testBit_false hm p.1.2).mp (by exact_mod_cast hB.symm.trans heB)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen ((p.2 (true, false)).val : ℕ) ?_ ?_ ?_
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
      exact ⟨by simp [color, hbitA, hbitB], rfl⟩
    · have hbitB : m.testBit p.1.2.val = true :=
        by
        cases h : m.testBit p.1.2.val
        · have he := (erase_eq_iff_testBit_false hm p.1.2).mpr h
          exact False.elim (hnB (by simpa [he] using hB))
        · rfl
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen ((p.2 (true, true)).val : ℕ) ?_ ?_ ?_
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
      exact ⟨by simp [color, hbitA, hbitB], rfl⟩
end ThreeSum.LightColorIndex
