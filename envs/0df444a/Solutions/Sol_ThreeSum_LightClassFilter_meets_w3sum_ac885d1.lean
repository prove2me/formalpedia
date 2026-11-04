-- Prove2me | solution 1 for ThreeSum.LightClassFilter.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:16.644682+00:00
-- url     : https://prove2.me/submissions/511b512c-4379-4c2f-8918-f276128e31c4

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Theorems.Thm_ThreeSum_LightClassFilter_items_succ
import Theorems.Thm_ThreeSum_LightClassFilter_items_length_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_Seg_update_out
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
attribute [local simp] ThreeSum.LightClassFilter.items_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightClassFilter
theorem _root_.solution {p src colors dst n want U : ℕ} {scale : ℤ} {μ : ℕ → ℤ} (hmain : P[p]? = some body) (x : ℕ → ℤ)
    (color : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (h3 : (3 : ℤ) ≤ lim.word) (hsrc : src + n ≤ dst)
    (hcolors : colors + n ≤ dst) (hspace : dst + (n + 1) ≤ lim.space) (hwant : want < 3) (hscale : |scale| ≤ 1)
    (hU : (U : ℤ) ≤ lim.word) (hread : ∀ i < n, μ (src + i) = x i)
    (hcolorRead : ∀ i < n, μ (colors + i) = (color i : ℤ)) (hcolorLt : ∀ i < n, color i < 3)
    (hbound : ∀ i < n, |x i| ≤ (U : ℤ)) :
    Meets lim P p d [src, colors, dst, n, want, scale] μ (time n)
      (fun r ν =>
        r = ((items x color want scale n).length : ℤ) ∧
          ν dst = ((items x color want scale n).length : ℤ) ∧
            Seg ν (dst + 1) (items x color want scale n) ∧ SameOutside μ ν dst (n + 1)) :=
  by
  have hscaleBounds := abs_le.mp hscale
  have hnWord : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : n ≤ lim.space)).trans hw
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
  repeat
    with_unfolding_none
      first
      | refine _root_.Light.Ends.seqAssoc ?_
      | refine _root_.Light.Ends.skipThen ?_
  refine
    Ends.pieceThen
      (Ends.for (lim := lim) (P := P) (d := d) (i := 7) (hi := v 3) (body := roundBody) (T := 100 * n + 50) (Q :=
        Inv μ x color src colors dst n want scale n) (Inv μ x color src colors dst n want scale) n 80 ?start ?round
        ?done ?bound (hT := by
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
      ?after
  case start => exact ⟨μ, by simp [update_frame_setLocal], by simp, SameOutside.refl⟩
  case round =>
    rintro j _ hj _ ⟨ν, rfl, hseg, hkeep⟩
    have hlen := items_length_le x color want scale j
    have hcr : ν (colors + j) = (color j : ℤ) := (hkeep _ (Or.inl (by omega))).trans (hcolorRead j hj)
    have hxr : ν (src + j) = x j := (hkeep _ (Or.inl (by omega))).trans (hread j hj)
    have hx : |scale * x j| ≤ lim.word := by
      rw [abs_mul]
      exact ((mul_le_mul hscale (hbound j hj) (abs_nonneg _) (by norm_num)).trans (by simpa using hU))
    have hxb := abs_le.mp hx
    have hc := hcolorLt j hj
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
      refine _root_.Light.Ends.iteIffThen (color j = want) (fun he => ?_) (fun hn => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcr]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcr] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcr] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hs : items x color want scale (j + 1) = items x color want scale j ++ [scale * x j] := by
        rw [items_succ, if_pos he]
      have hslen : (items x color want scale (j + 1)).length = (items x color want scale j).length + 1 := by simp [hs]
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen (dst + 1 + (items x color want scale j).length) (scale * x j) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hxr]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hxr] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hxr] <;> omega)
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
        refine _root_.Light.Ends.setToThen ((items x color want scale (j + 1)).length : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hslen]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hslen] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hslen] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine
        ⟨by simp, Function.update ν (dst + 1 + (items x color want scale j).length) (scale * x j), by
          simp [update_frame_setLocal], ?_, ?_⟩
      · rw [hs]
        exact hseg.snoc (scale * x j)
      · exact hkeep.update ⟨by omega, by omega⟩ _
    · have hs : items x color want scale (j + 1) = items x color want scale j := by
        rw [items_succ, if_neg hn, List.append_nil]
      with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp, ν, by simp [update_frame_setLocal, hs], by simpa [hs] using hseg, hkeep⟩
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨ν, rfl, hseg, hkeep⟩
    have hlen := items_length_le x color want scale n
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen dst ((items x color want scale n).length : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.setToThen ((items x color want scale n).length : ℕ) ?_ ?_ ?_
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
    exact ⟨by simp, by simp, hseg.update_out (Or.inl (by omega)) _, hkeep.update ⟨by omega, by omega⟩ _⟩
end ThreeSum.LightClassFilter
