-- Prove2me | solution 1 for ThreeSum.LightPascal.build_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:58.572277+00:00
-- url     : https://prove2.me/submissions/f1144dd3-5f3f-4fe3-acd7-f6679dad63e0

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_ThreeSum_LightPascal
import Theorems.Thm_ThreeSum_LightPascal_row_meets
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightPascal
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPascal
theorem _root_.solution {pBuild pFill pRow pLinear : ℕ} (hbuild : P[pBuild]? = some (buildBody pFill pRow))
    (hfill : P[pFill]? = some fillBody) (hrow : P[pRow]? = some (rowBody pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody) {μ : ℕ → ℤ} {dst L : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 1 < lim.depth) (hspace : dst + tableSize L ≤ lim.space) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pBuild d [dst, L] μ (buildTime L) fun _ μ' => Table μ' dst L ∧ SameOutside μ μ' dst (tableSize L) :=
  by
  have hsize : L + 1 ≤ tableSize L := by unfold tableSize; nlinarith
  have hfirst : dst + (L + 1) ≤ lim.space := by omega
  apply Meets.of_body hbuild
  unfold buildBody buildTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (L + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rowTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rowTime, LightArray.linearTime] <;> omega)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((fill_meets (d := d + 1) hfill (μ := μ) (dst := dst) (n := L + 1) (x := 0) hw hfirst) _ (by omega)) ?_ ?_ ?_
          ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (fill_meets (d := d + 1) hfill (μ := μ) (dst := dst) (n := L + 1) (x := 0) hw hfirst) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rowTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rowTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro res μ₁ ⟨hzero, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen dst 1 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rowTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rowTime, LightArray.linearTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  let μ₂ := Function.update μ₁ dst 1
  refine
    Ends.for (Inv μ dst L) L (rowTime L + 50) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rowTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨res, μ₂, ?_, ?_, ?_⟩
    · simp [μ₂, update_frame_setLocal]
    · intro a ha j hj
      have haz : a = 0 := by omega
      subst a
      simp only [Nat.zero_mul, Nat.add_zero]
      by_cases hjz : j = 0
      · subst j
        simp [μ₂]
      · rw [show μ₂ (dst + j) = μ₁ (dst + j) by exact Function.update_of_ne (by omega) _ _]
        have hh := hzero j (by simp; omega)
        simpa only [List.getElem_replicate, Nat.choose_eq_zero_of_lt (show 0 < j by omega), Nat.cast_zero] using hh
    · intro a ha
      rw [show μ₂ a = μ₁ a by exact Function.update_of_ne (by omega) _ _]
      exact hkept₁ a (by omega)
  case round =>
    rintro i _ hi _ ⟨r, μ', rfl, htable, hkept⟩
    have hrowBound : (i + 2) * (L + 1) ≤ tableSize L :=
      by
      have hm := Nat.mul_le_mul_right (L + 1) (show i + 2 ≤ L + 1 by omega)
      simpa only [tableSize, pow_two] using hm
    have hlow : 0 ≤ i * (L + 1) := Nat.zero_le _
    have hnext : (i + 1) * (L + 1) = i * (L + 1) + (L + 1) := by ring
    have hlast : (i + 2) * (L + 1) = (i + 1) * (L + 1) + (L + 1) := by ring
    have hcastI : (i : ℤ) * ((L : ℤ) + 1) = ((i * (L + 1) : ℕ) : ℤ) := by push_cast; rfl
    have hcastNext : ((i : ℤ) + 1) * ((L : ℤ) + 1) = (((i + 1) * (L + 1) : ℕ) : ℤ) :=
      by
      push_cast
      rfl
    have hcall :=
      row_meets (d := d + 1) (μ := μ') (src := dst + i * (L + 1)) (dst := dst + (i + 1) * (L + 1)) (L := L) (i := i)
        hrow hlinear hw hd (by omega) (by omega) (by left; omega) (by omega) hword (htable i le_rfl)
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rowTime,
              LightArray.linearTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [rowTime, LightArray.linearTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rowTime, LightArray.linearTime] <;> omega)
      on_goal -1 => (rintro resNew μ₃ ⟨hnew, hkept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, resNew, μ₃, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro a ha j hj
      by_cases hai : a = i + 1
      · subst a
        exact hnew j hj
      · have hai' : a ≤ i := by omega
        have hmul := Nat.mul_le_mul_right (L + 1) hai'
        rw [hkept₂ _ (by omega)]
        exact htable a hai' j hj
    · intro a ha
      exact (hkept₂ a (by omega)).trans (hkept a ha)
  case done =>
    rintro _ _ ⟨r, μ', rfl, htable, hkept⟩
    exact ⟨htable, hkept⟩
  case bound =>
    rintro i _ _ _ ⟨r, μ', rfl, _, _⟩
    simp
end ThreeSum.LightPascal
