-- Prove2me | solution 1 for actuarial_f_protected_state_epv_reconciles
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:02:06.012457+00:00
-- url     : https://prove2.me/submissions/21e8b18c-2735-428d-aa6c-5efd9fab059e

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedDirectEPV
import Definitions.Def_actuarial_f_gmpProtectedStateEPV
open ActuarialUnderpinsF

theorem solution
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) :
    gmpProtectedDirectEPV n h r g p disc a b c sa sb estate
       ga gb gc gs ge memberSupplement statutorySurvivor =
    gmpProtectedStateEPV n h r g p disc a b c sa sb estate
       ga gb gc gs ge memberSupplement statutorySurvivor := by
  unfold gmpProtectedDirectEPV gmpProtectedStateEPV expect ActuarialJointD.expect
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring
