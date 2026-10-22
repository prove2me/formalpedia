-- Prove2me | solution 1 for StaticQuote.Clairvoyant.sample_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:55:10.907846+00:00
-- url     : https://prove2.me/submissions/5f49a76a-6549-45a3-8a6b-e1ea664e4062

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Q : Model Ω)
    (y : ℕ → Ω → ℝ) (hy : Q.IsFCFSSchedule y) (ω : Ω) (M : ℕ) :
    Q.gamma 1 M ω / (M : ℝ≥0∞) ≤
      (∑ n ∈ Finset.Icc 1 M, ENNReal.ofReal (g Q.ce Q.cd (y n ω + Q.x n ω - Q.due n ω))) /
        (M : ℝ≥0∞) := by
  gcongr
  unfold Model.gamma
  refine iInf₂_le (fun n => y n ω) ⟨fun n hn => (hy ω n ?_).1, fun n hn => (hy ω n ?_).2⟩
  · simp only [Finset.mem_Icc] at hn; omega
  · simp only [Finset.mem_Ico] at hn; omega
