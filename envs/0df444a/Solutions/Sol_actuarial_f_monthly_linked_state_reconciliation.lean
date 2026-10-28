-- Prove2me | solution 1 for actuarial_f_monthly_linked_state_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:05:56.928995+00:00
-- url     : https://prove2.me/submissions/7ab8c94c-19cb-4d21-bd50-9c4d6f3132cc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyLinkedDirectEPV
import Definitions.Def_actuarial_f_monthlyLinkedStateEPV

open ActuarialUnderpinsF

theorem B1h_expect_sum (n h m : ℕ) (p : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ActuarialUnderpinsF.expect n h p (fun z i j => ∑ t ∈ Finset.range m, d t * F t z i j) =
      ∑ t ∈ Finset.range m, d t * ActuarialUnderpinsF.expect n h p (fun z i j => F t z i j) := by
  unfold ActuarialUnderpinsF.expect ActuarialJointD.expect
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem solution
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) :
    monthlyLinkedDirectEPV n h r g p disc a b c
        sa sb estate ga gb gc gs ge =
      monthlyLinkedStateEPV n h r g p disc a b c
        sa sb estate ga gb gc gs ge := by
  unfold monthlyLinkedDirectEPV monthlyLinkedStateEPV monthlyLinkedRealisedPV
  rw [B1h_expect_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  simp only [ActuarialUnderpinsF.expect, ActuarialJointD.expect, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  unfold monthlyLinkedInstalment estateInstalment
  ring
