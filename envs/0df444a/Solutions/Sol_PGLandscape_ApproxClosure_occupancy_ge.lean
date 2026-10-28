-- Prove2me | solution 1 for PGLandscape.ApproxClosure.occupancy_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:02:32.136187+00:00
-- url     : https://prove2.me/submissions/74af9ca3-9cbe-4dc2-89fa-548483fc31fe

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

open MeasureTheory ProbabilityTheory

theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    ∀ B : Set S, MeasurableSet B → ENNReal.ofReal (1 - M.γ) * M.ρ B ≤ PGLandscape.Closure.occupancy M π B := by
  intro B hB
  unfold PGLandscape.Closure.occupancy
  rw [Measure.sum_apply _ hB]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hid : (⇑(PGLandscape.Closure.iterKernel M π 0) : S → Measure S) = Measure.dirac := by
    funext s
    simp [PGLandscape.Closure.iterKernel, Kernel.id_apply]
  rw [Measure.smul_apply, hid, Measure.bind_dirac, pow_zero, mul_one, smul_eq_mul]
