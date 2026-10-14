-- Prove2me | solution 1 for actuarial_c_cont_immediate_death_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:11:52.939888+00:00
-- url     : https://prove2.me/submissions/723dad6f-dadf-4303-bde2-40905c68588b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_deathEPV
import Definitions.Def_actuarial_c_cont_deathSecondEPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Continuous
open MeasureTheory

theorem solution (μ : Measure ℝ) (n delta : ℝ) :
    deathSecondEPV μ n delta =
      deathEPV μ n (2*delta) := by
  have hp : (fun t : ℝ => (deathPV n delta t)^2) =
      (fun t : ℝ => deathPV n (2 * delta) t) := by
    funext t
    by_cases h : 0 ≤ t ∧ t < n
    · simp only [deathPV, if_pos h]
      calc
        (Real.exp (-delta * t))^2 =
            Real.exp (-delta * t) * Real.exp (-delta * t) := by ring
        _ = Real.exp ((-delta * t) + (-delta * t)) := by
            rw [Real.exp_add]
        _ = Real.exp (-(2 * delta) * t) := by
            congr 1
            ring
    · simp [deathPV, h]
  unfold deathSecondEPV deathEPV
  exact congrArg (fun f : ℝ → ℝ => ∫ t, f t ∂μ) hp
