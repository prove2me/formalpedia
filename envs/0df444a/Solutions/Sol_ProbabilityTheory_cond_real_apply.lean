-- Prove2me | solution 1 for ProbabilityTheory.cond_real_apply
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T20:42:58.102899+00:00
-- url     : https://prove2.me/submissions/5666076a-b981-41e3-b601-62fd45208928

import Mathlib

set_option maxHeartbeats 800000
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} {_ : MeasurableSpace Ω} {s : Set Ω}
    (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp only [measureReal_def]
  rw [cond_apply hms]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]

#check @solution
