-- Prove2me | solution 1 for actuarial_c_cont_continuous_terminal_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:14:17.190385+00:00
-- url     : https://prove2.me/submissions/2fb20adf-d4f7-4c56-b8da-6f4578881c8d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Continuous
open MeasureTheory

theorem solution (n delta t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    deathPV n delta t + maturityPV n delta t =
      Real.exp (-delta * exposure n t) := by
  by_cases h : t < n
  · have hcond : 0 ≤ t ∧ t < n := ⟨ht, h⟩
    have hnon : ¬ n ≤ t := not_le.mpr h
    have he : exposure n t = t := by
      simp [exposure, max_eq_right ht, min_eq_right h.le]
    simp [deathPV, maturityPV, hcond, hnon, he]
  · have hle : n ≤ t := le_of_not_gt h
    have hcond : ¬ (0 ≤ t ∧ t < n) := by
      intro hc
      exact h hc.2
    have he : exposure n t = n := by
      simp [exposure, max_eq_right ht, min_eq_left hle]
    simp [deathPV, maturityPV, hcond, hle, he]
