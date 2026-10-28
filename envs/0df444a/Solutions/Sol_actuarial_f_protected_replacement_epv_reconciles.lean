-- Prove2me | solution 1 for actuarial_f_protected_replacement_epv_reconciles
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:03:45.501622+00:00
-- url     : https://prove2.me/submissions/509f472b-40d1-458a-a7b7-08597b3f249a

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedDirectEPV
import Definitions.Def_actuarial_f_gmpProtectedReplacementEPV
import Definitions.Def_actuarial_f_gmpProtectedDisplaceableEPV
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
    gmpProtectedReplacementEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement statutorySurvivor +
    gmpProtectedDisplaceableEPV n h r g p disc a b sa sb gs
      statutorySurvivor := by
  unfold gmpProtectedDirectEPV gmpProtectedReplacementEPV gmpProtectedDisplaceableEPV expect ActuarialJointD.expect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold gmpProtectedParallelInstalment gmpProtectedReplacementInstalment gmpProtectedDisplaceableInstalment
  rw [← mul_add]
  congr 1
  unfold gmpProtectedSurvivorReplacement gmpProtectedSurvivorDisplaceable gmpProtectedSurvivorParallel
  split_ifs
  · rcases le_total (gmpProtectedContractualSurvivor h z i j t a b sa sb gs) (statutorySurvivor z i j t) with hh | hh
    · rw [max_eq_right hh, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hh, max_eq_right (by linarith)]; ring
  · ring
