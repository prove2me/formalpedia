-- Prove2me | solution 1 for ProphetBipartite.fact_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:01:38.300724+00:00
-- url     : https://prove2.me/submissions/6a446cc5-9b22-4bc0-9f2d-2477d7bac6cc

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Ω → ℝ) (hs : Integrable s P) :
    max (∫ ω, s ω ∂P) 0 ≤ ∫ ω, max (s ω) 0 ∂P := by
  have hmax_int : Integrable (fun ω => max (s ω) 0) P := hs.sup (integrable_const 0)
  refine max_le ?_ ?_
  · exact integral_mono hs hmax_int (fun ω => le_max_left (s ω) 0)
  · exact integral_nonneg (fun ω => le_max_right (s ω) 0)
