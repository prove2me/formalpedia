-- Prove2me | solution 1 for ResidualsDRO.Wass.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:23:31.941992+00:00
-- url     : https://prove2.me/submissions/9a293e4d-40f1-4fd4-9969-63c2dd01af9c

import Mathlib

set_option autoImplicit false

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V W : Ω → ℝ) (C₁ C₂ : ℝ) :
    P {ω | C₁ + C₂ < V ω + W ω} ≤ P {ω | C₁ < V ω} + P {ω | C₂ < W ω} := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_contra h
  push_neg at h
  linarith [h.1, h.2]
