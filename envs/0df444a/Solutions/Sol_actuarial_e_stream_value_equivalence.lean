-- Prove2me | solution 1 for actuarial_e_stream_value_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:22:59.256009+00:00
-- url     : https://prove2.me/submissions/23d1cf63-9af7-4f18-99ff-54122d32f269

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_contractEPV
import Definitions.Def_actuarial_e_cashflowEPV

open ActuarialDeathE

theorem solution (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : contractEPV h n e r g p disc service defer retire base a b c increase replace = cashflowEPV h n e r g p disc service defer retire base a b c increase replace := by
  have sw : ∀ F : ℕ → ℕ → ℕ → ℝ,
      (∑ t ∈ Finset.range n, disc t * ∑ i ∈ Finset.range (h + 1), ∑ j ∈ Finset.range (h + 1), p i j * F i j t)
      = ∑ i ∈ Finset.range (h + 1), ∑ j ∈ Finset.range (h + 1), p i j * ∑ t ∈ Finset.range n, disc t * F i j t := by
    intro F
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.range n)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := Finset.range n)]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by ring
  unfold contractEPV cashflowEPV deathEPV memberEPV spouseEPV guaranteeEPV realisedPV instalment ActuarialDeathE.expect ActuarialJointD.expect
  simp only [sw, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_add, Finset.sum_add_distrib]
  ring
