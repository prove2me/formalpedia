-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.integrable_of_cont
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:23:12.443257+00:00
-- url     : https://prove2.me/submissions/4d044572-268a-4e26-bb86-02ab98469bea

import Mathlib
variable {Γ : Type} [grp : Group Γ] [TopologicalSpace Γ]
include grp


theorem solution [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : MeasureTheory.Measure Γ)
    [MeasureTheory.IsFiniteMeasure μ] {f : Γ → ℂ} (hf : Continuous f) : MeasureTheory.Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
