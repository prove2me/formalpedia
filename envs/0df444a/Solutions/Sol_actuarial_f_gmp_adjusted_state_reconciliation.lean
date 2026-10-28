-- Prove2me | solution 1 for actuarial_f_gmp_adjusted_state_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:06:14.085571+00:00
-- url     : https://prove2.me/submissions/badb2f5c-4a3b-4c12-b128-e8ee056dfc72

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpAdjustedDirectEPV
import Definitions.Def_actuarial_f_gmpAdjustedStateEPV

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
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) :
    gmpAdjustedDirectEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement survivorSupplement =
    gmpAdjustedStateEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement survivorSupplement := by
  unfold gmpAdjustedDirectEPV gmpAdjustedStateEPV monthlyLinkedStateEPV
    gmpAdjustedParallelInstalment
  rw [B1h_expect_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [ActuarialUnderpinsF.expect, ActuarialJointD.expect, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  unfold monthlyLinkedInstalment estateInstalment
  ring
