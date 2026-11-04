-- Prove2me | solution 1 for ThreeSum.LightSourceBucketFromHistogram.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:12.129808+00:00
-- url     : https://prove2.me/submissions/83699a8e-eac6-45fd-a9c2-bd66af0035f1

import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketFromHistogram
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketFromHistogram
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ}
    (key : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hkeys : keys + N ≤ offsets)
    (hhist : hist + M ≤ offsets) (hoffsets : offsets + M + 1 ≤ cursor) (hcursor : cursor + M ≤ flat)
    (hspace : flat + N ≤ lim.space) (hkey : ∀ i < N, key i < M) (hread : ∀ i < N, μ (keys + i) = (key i : ℤ))
    (hhistRead : ∀ r < M, μ (hist + r) = (count key r N : ℤ)) :
    Meets lim P pMain d [keys, hist, offsets, cursor, flat, N, M] μ (time N M)
      (fun _ ν => Stored ν key N M offsets flat ∧ Kept μ ν offsets ∧ SameOutside μ ν offsets (flat + N - offsets)) :=
  by
  have hN : (N : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show N ≤ lim.space by omega)).trans hw
  apply Meets.of_body C.main
  unfold body time
  have ho :=
    LightSourceBucketOffsets.meets (d := d + 1) C.offsets (μ := μ) (hist := hist) (offsets := offsets) (cursor :=
      cursor) (M := M) (N := N) key hw hN hhist hoffsets (by omega) hkey hhistRead
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
    | refine _root_.Light.Ends.callToThen (ho _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen ho ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceBucketOffsets.time, LightSourceBucketScatter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₁ ⟨offRead, curRead, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hr : ∀ i < N, ν₁ (keys + i) = (key i : ℤ) := by
    intro i hi
    exact (kept₁ _ (Or.inl (by omega))).trans (hread i hi)
  have hs :=
    LightSourceBucketScatter.meets (d := d + 1) C.scatter (μ := ν₁) (keys := keys) (cursor := cursor) (flat := flat)
      (N := N) (M := M) key hw (by omega) hcursor hspace hkey hr curRead
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
    | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceBucketOffsets.time, LightSourceBucketScatter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₂ ⟨indices, _, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨⟨?_, indices⟩, ?_, ?_⟩
  · intro r hr
    exact (kept₂ _ (Or.inl (by omega))).trans (offRead r hr)
  · intro a ha
    exact (kept₂ a (Or.inl (by omega))).trans (kept₁ a (Or.inl ha))
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a (by omega))
end Procs
end ThreeSum.LightSourceBucketFromHistogram
