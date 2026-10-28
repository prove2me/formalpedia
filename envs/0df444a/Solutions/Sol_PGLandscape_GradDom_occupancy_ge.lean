-- Prove2me | solution 1 for PGLandscape.GradDom.occupancy_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:22:24.376986+00:00
-- url     : https://prove2.me/submissions/f61b0497-3dd1-4a55-8346-ac311b0e56ab

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

open MeasureTheory ProbabilityTheory

theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (B : Set S) (hB : MeasurableSet B) :
    ENNReal.ofReal (1 - M.γ) * M.ρ B ≤ PGLandscape.Closure.occupancy M π B := by
  unfold PGLandscape.Closure.occupancy
  rw [Measure.sum_apply _ hB]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hid : (⇑(PGLandscape.Closure.iterKernel M π 0) : S → Measure S) = Measure.dirac := by
    funext s
    simp [PGLandscape.Closure.iterKernel, Kernel.id_apply]
  rw [Measure.smul_apply, hid, Measure.bind_dirac, pow_zero, mul_one, smul_eq_mul]
