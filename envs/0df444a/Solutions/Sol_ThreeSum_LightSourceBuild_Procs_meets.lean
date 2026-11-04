-- Prove2me | solution 1 for ThreeSum.LightSourceBuild.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:02:12.089925+00:00
-- url     : https://prove2.me/submissions/225f13c0-4ab7-4f88-a27a-e76ef1a54a77

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBuild
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {src N raw flags n p m hist dst codes work U D E : ℕ} {shift : ℤ} (endpoint : ℕ → ℤ) (flag : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hp : 0 < p) (hm : 0 < m) (hsrc : src + N ≤ hist)
    (hraw : raw + n ≤ hist) (hflags : flags + n ≤ hist) (hhist : hist + m ≤ dst) (hdst : dst + n ≤ codes)
    (hcodes : codes + N ≤ work) (hspace : space work p U D E ≤ lim.space) (hshift : |shift| ≤ (D : ℤ))
    (hword : (word p m U D E : ℤ) ≤ lim.word) (hvalues : ∀ i < N, |μ (src + i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < n, μ (raw + i) = endpoint i) (hrawBound : ∀ i < n, |endpoint i| ≤ (E : ℤ))
    (hflagRead : ∀ i < n, μ (flags + i) = (flag i : ℤ)) (hflagBound : ∀ i < n, flag i ≤ 1) :
    Meets lim P pMain d [src, N, raw, flags, n, p, m, hist, dst, codes, work, shift] μ (time N n p m U D E)
      (fun _ ν =>
        (∀ i < n,
            ν (dst + i) =
              (LightSourceGather.value m endpoint flag
                  (fun r => LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src + j))) r N) i :
                ℤ)) ∧
          (∀ r < m,
              ν (hist + r) =
                (LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src + j))) r N : ℤ)) ∧
            Kept μ ν hist) :=
  by
  have hspaceH : LightSourceResidues.space work p U D ≤ lim.space := (le_max_left _ _).trans hspace
  have hspaceG : work + (Nat.log 2 (E + 1) + 2) ≤ lim.space := (le_max_right _ _).trans hspace
  have hwordH : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word :=
    by
    have hh : LightSourceResidues.word p m U D ≤ word p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwordG : (4 * E + 4 * m + 16 : ℤ) ≤ lim.word :=
    by
    have hh : 4 * E + 4 * m + 16 ≤ word p m U D E := by unfold word; omega
    exact (by exact_mod_cast hh : (4 * E + 4 * m + 16 : ℤ) ≤ (word p m U D E : ℤ)).trans hword
  have hcountWord : (N : ℤ) ≤ lim.word := by exact (Int.ofNat_le.mpr (by omega : N ≤ lim.space)).trans hw
  apply Meets.of_body S.main
  unfold body time
  have hh :=
    S.histogram.meets (d := d + 1) (μ := μ) (src := src) (hist := hist) (n := N) (p := p) (m := m) (codes := codes)
      (work := work) (U := U) (D := D) (shift := shift) hw (by omega) hp hm (by omega) (by omega) hcodes hspaceH hshift
      hwordH hvalues
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
    | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceHistogram.time,
            LightSourceResidues.time, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime, LightSourceGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceHistogram.time, LightSourceResidues.time, LightResidues.residueBudget,
              LightHistogram.histogramTime, LightHistogram.countTime, LightSourceGather.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceHistogram.time,
            LightSourceResidues.time, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime, LightSourceGather.time] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨_, counts, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have rawRead : ∀ i < n, ν₁ (raw + i) = endpoint i := by
    intro i hi
    exact (kept₁ _ ⟨by omega, Or.inl (by omega)⟩).trans (hrawRead i hi)
  have flagRead : ∀ i < n, ν₁ (flags + i) = (flag i : ℤ) :=
    by
    intro i hi
    exact (kept₁ _ ⟨by omega, Or.inl (by omega)⟩).trans (hflagRead i hi)
  have hg :=
    LightSourceGather.meets (d := d + 1) (μ := ν₁) (raw := raw) (flags := flags) (table := hist) (dst := dst) (n := n)
      (m := m) (work := work) (U := E) (B := N) S.gather S.histogram.emod endpoint flag
      (fun r => LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src + j))) r N) hw (by omega) hm
      (by omega) (by omega) hhist (by omega) hspaceG hwordG hcountWord rawRead hrawBound flagRead hflagBound counts
      (fun r _ => LightHistogram.count_le _ r N)
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
    | refine _root_.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceHistogram.time,
            LightSourceResidues.time, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime, LightSourceGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceHistogram.time, LightSourceResidues.time, LightResidues.residueBudget,
              LightHistogram.histogramTime, LightHistogram.countTime, LightSourceGather.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceHistogram.time,
            LightSourceResidues.time, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime, LightSourceGather.time] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨out, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨out, ?_, ?_⟩
  · intro r hr
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (counts r hr)
  · intro a ha
    exact (kept₂ a ⟨by omega, Or.inl (by omega)⟩).trans (kept₁ a ⟨by omega, Or.inl ha⟩)
end Procs
end ThreeSum.LightSourceBuild
