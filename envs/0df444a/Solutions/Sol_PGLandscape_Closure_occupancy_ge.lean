-- Prove2me | solution 1 for PGLandscape.Closure.occupancy_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:26:17.617032+00:00
-- url     : https://prove2.me/submissions/ab39902c-a60b-44bc-a94e-50cd234a6109

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

open MeasureTheory ProbabilityTheory

open PGLandscape.Closure in
theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : MDP S A)
    (π : MPolicy S A) :
    ∀ B : Set S, MeasurableSet B → ENNReal.ofReal (1 - M.γ) * M.ρ B ≤ occupancy M π B := by
  intro B hB
  rw [occupancy, Measure.sum_apply _ hB]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hid : (⇑(Kernel.id : Kernel S S)) = Measure.dirac := funext Kernel.id_apply
  simp only [Measure.smul_apply, smul_eq_mul, pow_zero, mul_one, iterKernel, hid,
    Measure.bind_dirac, le_refl]
