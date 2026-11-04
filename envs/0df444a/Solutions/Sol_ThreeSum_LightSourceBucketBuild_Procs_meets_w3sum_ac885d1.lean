-- Prove2me | solution 1 for ThreeSum.LightSourceBucketBuild.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:05.559333+00:00
-- url     : https://prove2.me/submissions/e097337e-8ec0-4b9b-b83b-f19dc81f0c6e

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_a9326e55c9f5f09c
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketBuild
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketBuild
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ}
    (key : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) (hkeys : keys + N ≤ offsets)
    (hhist : hist + M ≤ offsets) (hsep : Apart keys N hist M) (hoffsets : offsets + M + 1 ≤ cursor)
    (hcursor : cursor + M ≤ flat) (hspace : flat + N ≤ lim.space) (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys + i) = (key i : ℤ)) :
    Meets lim P pMain d [keys, hist, offsets, cursor, flat, N, M] μ (time N M)
      (fun _ ν =>
        Stored ν key N M offsets flat ∧
          (∀ r < M, ν (hist + r) = (count key r N : ℤ)) ∧ Kept μ ν hist ∧ SameOutside μ ν hist (flat + N - hist)) :=
  by
  apply Meets.of_body C.main
  unfold body time
  have hh :=
    histogram_meets (d := d + 1) C.histogram C.fill (μ := μ) (src := keys) (dst := hist) (n := N) (p := M) key hw
      (by omega) (by omega) (by omega) hsep hread hkey
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
    | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, histogramTime, countTime,
            LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time, LightSourceBucketScatter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [histogramTime, countTime, LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time,
              LightSourceBucketScatter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, histogramTime, countTime,
            LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time, LightSourceBucketScatter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₁ ⟨counts, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hr : ∀ i < N, ν₁ (keys + i) = (key i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hread i hi)
  have hb :=
    C.buckets.meets (d := d + 1) (μ := ν₁) (keys := keys) (hist := hist) (offsets := offsets) (cursor := cursor)
      (flat := flat) (N := N) (M := M) key hw (by omega) hkeys hhist hoffsets hcursor hspace hkey hr counts
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, histogramTime, countTime,
            LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time, LightSourceBucketScatter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [histogramTime, countTime, LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time,
              LightSourceBucketScatter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, histogramTime, countTime,
            LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time, LightSourceBucketScatter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₂ ⟨stored, kept₂, same₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨stored, ?_, ?_, ?_⟩
  · intro r hr
    exact (kept₂ _ (by omega)).trans (counts r hr)
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a (Or.inl ha))
  · intro a ha
    exact (same₂ a (by omega)).trans (kept₁ a (by omega))
end Procs
end ThreeSum.LightSourceBucketBuild
