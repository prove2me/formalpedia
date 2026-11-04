-- Prove2me | solution 1 for ThreeSum.LightNormalize.dedup_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:30.782232+00:00
-- url     : https://prove2.me/submissions/b346431f-b38f-4b1b-8f84-a4327b0bd39e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
import Theorems.Thm_ThreeSum_LightNormalize_sorted_head_not_mem
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightNormalize
theorem _root_.solution {pDedup : ℕ} (hprog : P[pDedup]? = some (dedupBody pDedup)) (hw : (lim.space : ℤ) ≤ lim.word)
    (h1 : (1 : ℤ) ≤ lim.word) :
    ∀ (L : List ℤ) (μ : ℕ → ℤ) (src dst d : ℕ),
      L.Pairwise (· ≤ ·) →
        Seg μ src L →
          src + L.length ≤ dst →
            dst + L.length ≤ lim.space →
              d + L.length ≤ lim.depth →
                Meets lim P pDedup d [src, L.length, dst] μ (dedupTime L.length)
                  (fun r μ' => r = (L.dedup.length : ℤ) ∧ Seg μ' dst L.dedup ∧ SameOutside μ μ' dst L.length) :=
  by
  intro L
  induction L with
  | nil =>
    intro μ src dst d hs hseg hsep hspace hd
    apply Meets.of_body hprog
    unfold dedupBody dedupTime
    refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
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
    exact ⟨rfl, Seg.nil, SameOutside.refl⟩
  | cons x zs ih =>
    intro μ src dst d hs hseg hsep hspace hd
    have hlen : (x :: zs).length = zs.length + 1 := rfl
    have hzs := hs.tail
    have hsource := (seg_cons.mp hseg).1
    have htail := (seg_cons.mp hseg).2
    have hsmall := (List.dedup_sublist zs).length_le
    have hemit :
      Ends lim P d (emitBody pDedup) ⟨frame [src, zs.length + 1, dst], μ⟩ (200 * zs.length + 180)
        (fun σ =>
          σ.loc 0 = ((x :: zs.dedup).length : ℤ) ∧
            Seg σ.mem dst (x :: zs.dedup) ∧ SameOutside μ σ.mem dst (zs.length + 1)) :=
      by
      unfold emitBody
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen dst x ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsource,
                dedupTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hsource, dedupTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsource, dedupTime] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      have htail' : Seg (Function.update μ dst x) (src + 1) zs :=
        by
        intro i hi
        rw [Function.update_of_ne (by omega)]
        exact htail i hi
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
              ((ih (Function.update μ dst x) (src + 1) (dst + 1) (d + 1) hzs htail' (by omega) (by omega) (by omega)) _
                (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            _root_.Light.Ends.callToThen
              (ih (Function.update μ dst x) (src + 1) (dst + 1) (d + 1) hzs htail' (by omega) (by omega) (by omega)) ?_
              ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dedupTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [dedupTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dedupTime] <;> omega)
        on_goal -1 => (rintro count μ' ⟨hcount, hout, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (zs.dedup.length + 1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, dedupTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hcount, dedupTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, dedupTime] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, ?_, ?_⟩
      · rw [seg_cons]
        refine ⟨?_, hout⟩
        change μ' dst = x
        rw [hkeep dst (Or.inl (by omega)), Function.update_self]
      · intro a ha
        change μ' a = μ a
        rw [hkeep a (by omega), Function.update_of_ne (by omega)]
    apply Meets.of_body hprog
    unfold dedupBody dedupTime
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
    cases zs with
    | nil =>
      refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
      simpa using
        hemit.mono
          (by
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
          (fun _ h => h)
    | cons y ys =>
      have hysLen : (y :: ys).length = ys.length + 1 := rfl
      have hnext : μ (src + 1) = y := (seg_cons.mp htail).1
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen (x = y) (fun hxy => ?_) (fun hxy => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsource, hnext,
                dedupTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hsource, hnext, dedupTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsource, hnext, dedupTime] <;> omega)
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · have hdedup : (x :: y :: ys).dedup = (y :: ys).dedup := List.dedup_cons_of_mem (by simp [hxy])
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
                ((ih μ (src + 1) dst (d + 1) hzs htail (by omega) (by omega) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
          |
            refine
              _root_.Light.Ends.callToThen (ih μ (src + 1) dst (d + 1) hzs htail (by omega) (by omega) (by omega)) ?_ ?_
                ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dedupTime]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [dedupTime] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dedupTime] <;> omega)
          on_goal -1 =>
            (rintro count μ' ⟨hcount, hout, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        refine ⟨by simpa [hdedup] using hcount, by simpa [hdedup] using hout, ?_⟩
        exact hkeep.mono le_rfl (by simp)
      · have hdedup : (x :: y :: ys).dedup = x :: (y :: ys).dedup :=
          List.dedup_cons_of_notMem (sorted_head_not_mem hs hxy)
        focus
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
          first
          | refine _root_.Light.Ends.pieceThen hemit ?_ ?_
          | refine _root_.Light.Ends.pieceLast hemit ?_ ?_
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
          on_goal -1 => rintro σ h
        with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simpa [hdedup] using h.1, by simpa [hdedup] using h.2.1, h.2.2⟩
end ThreeSum.LightNormalize
