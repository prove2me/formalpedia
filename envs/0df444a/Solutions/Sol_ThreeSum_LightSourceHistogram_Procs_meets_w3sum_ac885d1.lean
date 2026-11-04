-- Prove2me | solution 1 for ThreeSum.LightSourceHistogram.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:22.013082+00:00
-- url     : https://prove2.me/submissions/97b0f8ae-8a19-43f7-8c3e-7a0786055998

import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_a9326e55c9f5f09c
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceHistogram
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceHistogram
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) (hp : 0 < p) (hm : 0 < m) (hsrc : src + n ≤ codes)
    (hhist : hist + m ≤ codes) (hcodes : codes + n ≤ work) (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, hist, n, p, m, codes, work, shift] μ (time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes + i) = (LightSourceResidues.key p m shift (μ (src + i)) : ℤ)) ∧
          (∀ r < m,
              ν (hist + r) =
                (LightHistogram.count (fun i => LightSourceResidues.key p m shift (μ (src + i))) r n : ℤ)) ∧
            KeptBut μ ν codes hist m) :=
  by
  have hwork : work ≤ lim.space := by
    unfold LightSourceResidues.space at hspace
    omega
  apply Meets.of_body S.main
  unfold body time
  have hkeys :=
    LightSourceResidues.meets (d := d + 1) (μ := μ) (src := src) (dst := codes) (n := n) (p := p) (m := m) (work :=
      work) (U := U) (D := D) (shift := shift) S.keys S.emod hw hd hp hm (by omega) hcodes hspace (Or.inl hsrc) hshift
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
    | refine _root_.Light.Ends.callToThen (hkeys _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hkeys ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceResidues.time,
            LightResidues.residueBudget, LightHistogram.histogramTime, LightHistogram.countTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceResidues.time, LightResidues.residueBudget, LightHistogram.histogramTime,
              LightHistogram.countTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceResidues.time,
            LightResidues.residueBudget, LightHistogram.histogramTime, LightHistogram.countTime] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨keys, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hhistogram :=
    LightHistogram.histogram_meets (d := d + 1) (μ := ν₁) (src := codes) (dst := hist) (n := n) (p := m) S.histogram
      S.fill (fun i => LightSourceResidues.key p m shift (μ (src + i))) hw hd (by omega) (by omega) (Or.inr hhist) keys
      (fun i _ => LightSourceResidues.key_lt hm shift (μ (src + i)))
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
    | refine _root_.Light.Ends.callToThen (hhistogram _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hhistogram ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceResidues.time,
            LightResidues.residueBudget, LightHistogram.histogramTime, LightHistogram.countTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceResidues.time, LightResidues.residueBudget, LightHistogram.histogramTime,
              LightHistogram.countTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceResidues.time,
            LightResidues.residueBudget, LightHistogram.histogramTime, LightHistogram.countTime] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨counts, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, counts, ?_⟩
  · intro i hi
    exact (kept₂ _ (Or.inr (by omega))).trans (keys i hi)
  · intro a ⟨ha, hout⟩
    exact (kept₂ a hout).trans (kept₁ a ⟨by omega, Or.inl ha⟩)
end Procs
end ThreeSum.LightSourceHistogram
