-- Prove2me | solution 1 for actuarial_c_cont_continuous_path_conservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:15:42.879003+00:00
-- url     : https://prove2.me/submissions/576fae19-e432-491c-bebf-2ca86ca09010

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV
import Definitions.Def_actuarial_c_cont_continuousAnnuityPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Continuous
open MeasureTheory

theorem solution (n delta t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    deathPV n delta t + maturityPV n delta t +
      delta * continuousAnnuityPV n delta t = 1 := by
  have hterminal : deathPV n delta t + maturityPV n delta t =
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
  calc
    deathPV n delta t + maturityPV n delta t +
      delta * continuousAnnuityPV n delta t =
        Real.exp (-delta * exposure n t) +
          delta * continuousAnnuityPV n delta t := by rw [hterminal]
    _ = 1 := by
      by_cases hd : delta = 0
      · simp [continuousAnnuityPV, hd]
      · simp only [continuousAnnuityPV, if_neg hd]
        field_simp [hd] <;> ring
