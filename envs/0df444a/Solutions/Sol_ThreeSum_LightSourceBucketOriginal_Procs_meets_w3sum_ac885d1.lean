-- Prove2me | solution 1 for ThreeSum.LightSourceBucketOriginal.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:05.202199+00:00
-- url     : https://prove2.me/submissions/2455c7b9-8459-4314-b625-1c5a06ace7b8

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOriginal
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketOriginal
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ}
    {src N p m hist codes offsets cursor flat work U D : ℕ} {shift : ℤ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 2 < lim.depth) (hp : 0 < p) (hm : 0 < m) (hsrc : src + N ≤ hist) (hhist : hist + m ≤ codes)
    (hcodes : codes + N ≤ offsets) (hoffsets : offsets + m + 1 ≤ cursor) (hcursor : cursor + m ≤ flat)
    (hflat : flat + N ≤ work) (hspace : LightSourceResidues.space work p U D ≤ lim.space) (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word) (hvalues : ∀ i < N, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [(src : ℤ), (N : ℤ), (p : ℤ), (m : ℤ), shift, (hist : ℤ), (codes : ℤ), (offsets : ℤ), (cursor : ℤ), (flat : ℤ),
        (work : ℤ)]
      μ (time N p m U D)
      (fun _ ν =>
        Stored ν (fun i => LightSourceResidues.key p m shift (μ (src + i))) N m offsets flat ∧
          (∀ r < m, ν (hist + r) = (count (fun i => LightSourceResidues.key p m shift (μ (src + i))) r N : ℤ)) ∧
            (∀ i < N, ν (codes + i) = (LightSourceResidues.key p m shift (μ (src + i)) : ℤ)) ∧ Kept μ ν hist) :=
  by
  have hwork : work ≤ lim.space := by
    unfold LightSourceResidues.space at hspace
    omega
  apply Meets.of_body C.main
  unfold body time
  have hs :=
    C.sourceProcs.meets (d := d + 1) (μ := μ) (src := src) (hist := hist) (n := N) (p := p) (m := m) (codes := codes)
      (work := work) (U := U) (D := D) (shift := shift) hw (by omega) hp hm (by omega) hhist (by omega) hspace hshift
      hword hvalues
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceHistogram.time,
            LightSourceResidues.time, LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceHistogram.time, LightSourceResidues.time, LightSourceBucketFromHistogram.time,
              LightSourceBucketOffsets.time, LightSourceBucketScatter.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceHistogram.time,
            LightSourceResidues.time, LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨keys, counts, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hb :=
    C.buckets.meets (d := d + 1) (μ := ν₁) (keys := codes) (hist := hist) (offsets := offsets) (cursor := cursor)
      (flat := flat) (N := N) (M := m) (fun i => LightSourceResidues.key p m shift (μ (src + i))) hw (by omega) hcodes
      (by omega) hoffsets hcursor (by omega) (fun i _ => LightSourceResidues.key_lt hm shift (μ (src + i))) keys counts
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceHistogram.time,
            LightSourceResidues.time, LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceHistogram.time, LightSourceResidues.time, LightSourceBucketFromHistogram.time,
              LightSourceBucketOffsets.time, LightSourceBucketScatter.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceHistogram.time,
            LightSourceResidues.time, LightSourceBucketFromHistogram.time, LightSourceBucketOffsets.time,
            LightSourceBucketScatter.time] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨stored, kept₂, _⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨stored, ?_, ?_, ?_⟩
  · intro r hr
    exact (kept₂ _ (by omega)).trans (counts r hr)
  · intro i hi
    exact (kept₂ _ (by omega)).trans (keys i hi)
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a ⟨by omega, Or.inl ha⟩)
end Procs
end ThreeSum.LightSourceBucketOriginal
