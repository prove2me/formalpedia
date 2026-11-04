-- Prove2me | solution 1 for ThreeSum.LightPairSearch.row_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:10.109283+00:00
-- url     : https://prove2.me/submissions/f273c0d4-8804-4858-b26a-6e34174b3623

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightPairSearch_first_le
import Theorems.Thm_ThreeSum_LightPairSearch_goodCode_pair
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 300000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightPairSearch
theorem _root_.solution {pRow pPred q u ctx T d : ℕ} (hrow : P[pRow]? = some (rowBody pPred)) (good : ℕ → ℕ → Prop)
    [DecidableRel good] (I : (ℕ → ℤ) → Prop) (hq : 0 < q) (hu : u < q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q * q + q + ctx + 20 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hpred :
      ∀ v < q,
        ∀ ν, I ν → Meets lim P pPred (d + 1) [u, v, ctx] ν T (fun r ξ => r = (if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim P pRow d [q, u, ctx, first (goodCode q good) (u * q)] μ (rowTime q T)
      (fun r ν => r = (first (goodCode q good) ((u + 1) * q) : ℤ) ∧ I ν) :=
  by
  have hqW : (q : ℤ) ≤ lim.word := by omega
  have huW : (u : ℤ) ≤ lim.word := by omega
  have hctxW : (ctx : ℤ) ≤ lim.word := by omega
  have hcode (j : ℕ) (hj : j ≤ q) : u * q + j ≤ q * q :=
    by
    have hh := Nat.mul_le_mul_right q (show u + 1 ≤ q by omega)
    nlinarith
  apply Meets.of_body hrow
  unfold rowBody rowTime
  refine
    Ends.pieceThen
      (Ends.for (T := q * (T + 100) + 10) (Q := RowInv I q u ctx good q) (RowInv I q u ctx good) q (T + 80) ?_ ?_ ?_ ?_
        (hT := by
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
      ?_ (hT := by
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
  · refine ⟨0, μ, ?_, hI⟩
    simp only [Nat.add_zero, update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc, μ⟩ : State)) (frame_append_zeros _ 1).symm
  · rintro j _ hj _ ⟨rval, ν, rfl, hν⟩
    have hprefix := first_le (goodCode q good) (u * q + j)
    have hprefixNext := first_le (goodCode q good) (u * q + (j + 1))
    have hjW : (j : ℤ) ≤ lim.word := by omega
    have hsmall := hcode j (by omega)
    have hsmallNext := hcode (j + 1) (by omega)
    have hprod : ((u * q : ℕ) : ℤ) ≤ lim.word := by omega
    have hcodeW : ((u * q + j + 1 : ℕ) : ℤ) ≤ lim.word := by omega
    have hprefW : ((first (goodCode q good) (u * q + j) : ℕ) : ℤ) ≤ lim.word := by omega
    have hgood := goodCode_pair q u j hq hj good
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen (first (goodCode q good) (u * q + j) = 0) (fun hz => ?_) (fun hnz => ?_) ?_ ?_
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
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        first
        | refine _root_.Light.Ends.callToThen ((hpred j hj ν hν) _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen (hpred j hj ν hν) ?_ ?_ ?_ ?_
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
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
        on_goal -1 => (rintro result ξ ⟨hr, hξ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      by_cases hg : good u j
      · have hr' : result = 1 := by simpa only [hg, ite_true] using hr
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < result) (fun hpos => ?_) (fun hnonpos => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr']
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hr'] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr'] <;> omega)
          all_goals
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_
        · focus
            ((first
                | refine _root_.Light.Ends.seqSelf ?_
                | refine _root_.Light.Ends.skipLast ?_);
              repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_)
            refine _root_.Light.Ends.setToThen (u * q + j + 1 : ℕ) ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, Nat.add_assoc]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [Nat.add_assoc] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, Nat.add_assoc] <;> omega)
            try with_unfolding_none refine _root_.Light.Ends.skip ?_
          refine ⟨by simp, 1, ξ, ?_, hξ⟩
          have hgc := hgood.mpr hg
          simp [first, hz, hgc, update_frame_setLocal, Nat.add_assoc, hr']
        · omega
      · have hr' : result = 0 := by simpa only [hg, ite_false] using hr
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < result) (fun hpos => ?_) (fun hnonpos => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr']
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hr'] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr'] <;> omega)
          all_goals
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_
        · omega
        · apply Ends.skip
          refine ⟨by simp, 0, ξ, ?_, hξ⟩
          have hgc : ¬goodCode q good (u * q + j) := by simpa only [hgood] using hg
          simp [first, hz, hgc, update_frame_setLocal, Nat.add_assoc, hr']
    · apply Ends.skip
      refine ⟨by simp, rval, ν, ?_, hν⟩
      simp [first, hnz, update_frame_setLocal, Nat.add_assoc]
  · intro σ _ hshape; exact hshape
  · rintro j _ hj _ ⟨rval, ν, rfl, hν⟩; simp
  · rintro σ ⟨rval, ν, rfl, hν⟩
    have hb := first_le (goodCode q good) (u * q + q)
    have hsmall := hcode q le_rfl
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (first (goodCode q good) ((u + 1) * q) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, Nat.add_mul,
              Nat.one_mul]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [Nat.add_mul, Nat.one_mul] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, Nat.add_mul, Nat.one_mul] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, hν⟩
end ThreeSum.LightPairSearch
