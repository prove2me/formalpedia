-- Prove2me | solution 1 for ThreeSum.LightSourceBucketSetup.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:10.318935+00:00
-- url     : https://prove2.me/submissions/699e8bac-b22c-4fcd-9067-c080e80899e8

import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketSetup
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketSetup
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ} {keys N M base : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hM : 0 < M) (hkeys : keys + N ≤ base)
    (hspace : next base N M ≤ lim.space) (hkey : ∀ i < N, key i < M) (hread : ∀ i < N, μ (keys + i) = (key i : ℤ)) :
    Meets lim P pMain d [keys, N, M, base] μ (time N M)
      (fun r ν =>
        r = (next base N M : ℤ) ∧
          Stored ν key N M (offsets base M) (flat base M) ∧
            (∀ j < M, ν (hist base + j) = (count key j N : ℤ)) ∧ Kept μ ν base) :=
  by
  have hspace' : base + 3 * M + 1 + N ≤ lim.space := hspace
  have htwo : (2 * (M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 2 * M ≤ lim.space by omega) : (2 * (M : ℤ)) ≤ lim.space).trans hw
  have hthree : (3 * (M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3 * M ≤ lim.space by omega) : (3 * (M : ℤ)) ≤ lim.space).trans hw
  apply Meets.of_body C.main
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
    refine _root_.Light.Ends.setToThen (offsets base M : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, offsets]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [offsets] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, offsets] <;> omega)
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
    refine _root_.Light.Ends.setToThen (cursor base M : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cursor]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cursor] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cursor] <;> omega)
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
    refine _root_.Light.Ends.setToThen (flat base M : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, flat]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [flat] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, flat] <;> omega)
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
    refine _root_.Light.Ends.setToThen (next base N M : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, next, flat]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [next, flat] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, next, flat] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hb :=
    C.build.meets (d := d + 1) (μ := μ) (keys := keys) (hist := hist base) (offsets := offsets base M) (cursor :=
      cursor base M) (flat := flat base M) (N := N) (M := M) key hw (by omega) (by unfold offsets; omega)
      (by unfold hist offsets; omega) (Or.inl hkeys) (by unfold offsets cursor; omega) (by unfold cursor flat; omega)
      hspace hkey hread
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
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceBucketBuild.time, hist, offsets,
            cursor, flat, next]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceBucketBuild.time, hist, offsets, cursor, flat, next] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceBucketBuild.time, hist, offsets,
            cursor, flat, next] <;>
          omega)
    on_goal -1 => (rintro r ν ⟨stored, counts, kept, _⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (next base N M : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, next]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [next] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, next] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, stored, counts, kept⟩
end Procs
end ThreeSum.LightSourceBucketSetup
