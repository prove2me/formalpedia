-- Prove2me | solution 1 for ProbabilityTheory.cond_isProbabilityMeasure_of_real
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T05:53:01.097419+00:00
-- url     : https://prove2.me/submissions/8eaa2730-a5f8-4ac8-a08c-58e99811808d

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by
  have h0 : μ s ≠ 0 := by
    intro h
    exact hcs (by simp [measureReal_def, h])
  have htop : μ s ≠ ⊤ := by
    intro h
    exact hcs (by simp [measureReal_def, h])
  exact cond_isProbabilityMeasure_of_finite h0 htop
