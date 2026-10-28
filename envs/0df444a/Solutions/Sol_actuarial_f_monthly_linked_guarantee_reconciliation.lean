-- Prove2me | solution 1 for actuarial_f_monthly_linked_guarantee_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:02:31.949952+00:00
-- url     : https://prove2.me/submissions/c16fa080-59c0-48e2-b24f-7a3d7253a46b

import Mathlib
import Definitions.Def_actuarial_f_guaranteeOverlapEPV
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_monthlyLinkedDirectEPV
import Definitions.Def_actuarial_f_monthlyLinkedReplacementEPV
open ActuarialUnderpinsF

theorem solution
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) :
    monthlyLinkedDirectEPV n h r g p disc a b c
        sa sb estate ga gb gc gs ge =
      monthlyLinkedReplacementEPV n h r g p disc a b c
        sa sb estate ga gb gc gs ge +
      guaranteeOverlapEPV n h r g p disc
        (linkedSpouseBasis a b sa sb) gs := by
  unfold monthlyLinkedDirectEPV monthlyLinkedReplacementEPV guaranteeOverlapEPV expect ActuarialJointD.expect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  unfold monthlyLinkedRealisedPV
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold monthlyLinkedInstalment replacementPayment
  split_ifs <;> ring
