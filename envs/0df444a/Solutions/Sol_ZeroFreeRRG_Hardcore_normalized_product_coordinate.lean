-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.normalized_product_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:10:36.271198+00:00
-- url     : https://prove2.me/submissions/22f69bb4-523e-49b4-896f-a33470549b8f

import Theorems.Thm_ZeroFreeRRG_Hardcore_product_coordinate_integral
import Mathlib
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a φ : ℝ → ℝ) (ha : (∫ x, a x ∂μ) = 1) (i : Fin d) :
    (∫ xs : Fin d → ℝ, (∏ j, a (xs j)) * φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = ∫ x, a x * φ x ∂μ := by
  have h := product_coordinate_integral d μ (fun _ => a) φ i
  simpa [ha] using h
