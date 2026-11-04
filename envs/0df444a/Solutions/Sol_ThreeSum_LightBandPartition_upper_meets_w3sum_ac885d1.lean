-- Prove2me | solution 1 for ThreeSum.LightBandPartition.upper_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:27.633845+00:00
-- url     : https://prove2.me/submissions/8ab58b39-6f51-44c4-97c8-de83fed2ea66

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_Light_wrote_succ
import Theorems.Thm_Light_wrote_zero
import Theorems.Thm_ThreeSum_BandPartition_size_le
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPartition
theorem _root_.solution {p src dst n g d : ℕ} (hp : P[p]? = some upperBody) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g) (hsrc : src + n ≤ dst) (hdst : dst + size n g ≤ lim.space)
    (hword : ((n + g + 2 : ℕ) : ℤ) ≤ lim.word) (hread : ∀ i < n, μ (src + i) = f i) :
    Meets lim P p d [src, n, g, dst, size n g] μ (upperTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst + i) = f (stop n g i - 1)) ∧ SameOutside μ μ' dst (size n g)) :=
  by
  let F := fun i => f (stop n g i - 1)
  apply Meets.of_body hp
  unfold upperBody upperTime
  refine
    Ends.for (fun i σ => ∃ q : ℕ, σ = ⟨frame [src, n, g, dst, size n g, i, q], wrote μ dst F i⟩) (size n g) 92 ?start
      ?round ?done ?bound
  case start =>
    refine ⟨0, ?_⟩
    simp [update_frame_setLocal, wrote_zero]
    simpa using (frame_append_zeros [src, n, g, dst, size n g, 0] 1).symm
  case round =>
    rintro i _ hi _ ⟨q, rfl⟩
    have hidx : i * g < n := start_lt hg hi
    have hsmall : size n g ≤ n := size_le _ _
    have hnextBound : (i + 1) * g ≤ n + g := by nlinarith
    have hnextNonneg : (0 : ℤ) ≤ ((i : ℤ) + 1) * (g : ℤ) := by positivity
    have hnextWord : ((i : ℤ) + 1) * (g : ℤ) ≤ lim.word := by
      exact
        (by exact_mod_cast (show (i + 1) * g ≤ n + g + 2 by omega) :
              ((i : ℤ) + 1) * (g : ℤ) ≤ ((n + g + 2 : ℕ) : ℤ)).trans
          hword
    have hstopN := stop_le n g i
    have hstopPos : 0 < stop n g i := by have := start_lt_stop hg hi; omega
    have hstopI := stop_sub_one_lt hg hi
    have hstore (q : ℕ) (hq : q = stop n g i) :
      Ends lim P d
        (.store ((_root_.Light.Expr.op _root_.Light.Op.add) (v 3) (v 5))
          (M
            ((_root_.Light.Expr.op _root_.Light.Op.sub) ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 6))
              (k 1))))
        ⟨frame [src, n, g, dst, size n g, i, q], wrote μ dst F i⟩ 40
        (fun σ =>
          σ.loc 5 = (i : ℤ) ∧
            ∃ r : ℕ,
              { σ with loc := Function.update σ.loc 5 ((i : ℤ) + 1) } =
                ⟨frame [src, n, g, dst, size n g, i + 1, r], wrote μ dst F (i + 1)⟩) :=
      by
      subst q
      have haddr : ((src : ℤ) + (stop n g i : ℤ) - 1).toNat = src + (stop n g i - 1) := by
        rw [show (src : ℤ) + (stop n g i : ℤ) - 1 = ((src + (stop n g i - 1) : ℕ) : ℤ) by omega, Int.toNat_natCast]
      have hr : wrote μ dst F i (src + (stop n g i - 1)) = F i :=
        by
        rw [wrote_rest (by omega)]
        exact hread _ hstopI
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen (dst + i) (F i) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr, hr]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [haddr, hr] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hr] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp, stop n g i, by simp [update_frame_setLocal, wrote_succ]⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen ((i + 1) * g : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.iteIffThen ((n : ℤ) < (((i + 1) * g : ℕ) : ℤ)) (fun hn => ?_) (fun hn => ?_) ?_ ?_
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
    · have hmin : stop n g i = n := by unfold stop; omega
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_
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
        (refine
            _root_.Light.Ends.pieceLast (hstore n hmin.symm)
              (fun _ h_p2m_16336726232280953526 => h_p2m_16336726232280953526) ?_;
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
                  | (ring_nf; omega)))
    · have hmin : stop n g i = (i + 1) * g := by unfold stop; omega
      focus
        (refine
            _root_.Light.Ends.pieceLast (hstore ((i + 1) * g) hmin.symm)
              (fun _ h_p2m_17433793211965132687 => h_p2m_17433793211965132687) ?_;
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
                  | (ring_nf; omega)))
  case done =>
    rintro _ _ ⟨q, rfl⟩
    exact
      ⟨fun i hi => wrote_done (μ := μ) (dst := dst) (f := F) hi, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_7687293917356272104 hx_p2m_7687293917356272104
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_8510420641433705029);
                    (try have := h_p2m_8510420641433705029 x_p2m_7687293917356272104 (by omega));
                    revert h_p2m_8510420641433705029)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_7687293917356272104;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_7618164760106382532);
                    (try have := h_p2m_7618164760106382532 x_p2m_7687293917356272104 (by omega));
                    revert h_p2m_7618164760106382532)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_2061455507903240054);
                    (try have := h_p2m_2061455507903240054 x_p2m_7687293917356272104 (by omega));
                    revert h_p2m_2061455507903240054)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
  case bound =>
    rintro i _ _ _ ⟨q, rfl⟩
    simp
end ThreeSum.LightBandPartition
