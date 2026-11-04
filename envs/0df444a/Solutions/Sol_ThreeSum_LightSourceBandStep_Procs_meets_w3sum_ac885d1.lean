-- Prove2me | solution 1 for ThreeSum.LightSourceBandStep.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:37:45.978108+00:00
-- url     : https://prove2.me/submissions/bf58da62-a368-4681-b397-aae0f0b26576

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
import Definitions.Def_WeightedCache3SUM_Alias_ef4fef510485d373
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_BandPartition_size_le
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandStep
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandStep
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ} {src n g p m base U D i : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth) (hg : 0 < g) (hp : 0 < p) (hm : 0 < m)
    (hi : i < size n g) (hsrc : src + n ≤ base) (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word n g p m U D : ℤ) ≤ lim.word) (hread : ∀ j < n, μ (src + j) = f j)
    (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [src, n, g, p, m, shift, base, cap n g, size n g, data base n g, stride n g m, work base n g m, i] μ
      (time n g p m U D)
      (fun _ ν => SourceBandData.At ν f base n g p m shift i ∧ KeptBut μ ν (hist base n g m i) (base + 6 * i) 6) :=
  by
  have hidx : i * g < n := start_lt hg hi
  have hcount := size_le n g
  have hnext : (i + 1) * g ≤ n + g := by nlinarith
  have hwordN : ((n + g + 2 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n + g + 2 ≤ word n g p m U D by unfold word; omega)).trans hword
  have hprod : (i : ℤ) * (g : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show i * g ≤ n + g + 2 by omega) : (i : ℤ) * (g : ℤ) ≤ ((n + g + 2 : ℕ) : ℤ)).trans hwordN
  have hprodN : (0 : ℤ) ≤ (i : ℤ) * (g : ℤ) := by positivity
  have hnextZ : ((i : ℤ) + 1) * (g : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show (i + 1) * g ≤ n + g + 2 by omega) : ((i : ℤ) + 1) * (g : ℤ) ≤ ((n + g + 2 : ℕ) : ℤ)).trans
      hwordN
  have hnextN : (0 : ℤ) ≤ ((i : ℤ) + 1) * (g : ℤ) := by positivity
  have htailTime : tailTime n g p m U D = charge n g p m U D + 1000 := rfl
  apply Meets.of_body C.main
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (start g i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, start, tailTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [start, tailTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, start, tailTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen ((i + 1) * g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, tailTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [tailTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tailTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.iteIffThen ((n : ℤ) < (((i + 1) * g : ℕ) : ℤ)) (fun hlarge => ?_) (fun hlarge => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, tailTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [tailTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tailTime] <;> omega)
    all_goals
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
  · have hmin : n = stop n g i := by unfold stop; omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, tailTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [tailTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tailTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      (refine
          _root_.Light.Ends.pieceLast
            (tail_ends C.original (last := n) f hw hd hg hp hm hi hsrc hmin hspace hshift hword hread hvalues)
            (fun _ h_p2m_18040256439399135496 => h_p2m_18040256439399135496) ?_;
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;> first
                | omega
                | (ring_nf; omega)))
  · have hmin : (i + 1) * g = stop n g i := by unfold stop; omega
    focus
      (refine
          _root_.Light.Ends.pieceLast
            (tail_ends C.original (last := (i + 1) * g) f hw hd hg hp hm hi hsrc hmin hspace hshift hword hread hvalues)
            (fun _ h_p2m_15357048996109476613 => h_p2m_15357048996109476613) ?_;
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;> first
                | omega
                | (ring_nf; omega)))
end Procs
end ThreeSum.LightSourceBandStep
