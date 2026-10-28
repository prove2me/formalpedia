-- Prove2me | solution 1 for actuarial_f_direct_replacement_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:54.466153+00:00
-- url     : https://prove2.me/submissions/a251d581-6e29-4528-802c-f9668d176caa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_directEPV
import Definitions.Def_actuarial_f_guaranteeOverlapEPV
import Definitions.Def_actuarial_f_replacementEPV

open ActuarialUnderpinsF

theorem solution
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ)
    (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    directEPV n h r g p disc a b c s estate g0 g1 gs ge =
      replacementEPV n h r g p disc a b c s estate g0 g1 gs ge +
      guaranteeOverlapEPV n h r g p disc s gs := by
  unfold directEPV replacementEPV guaranteeOverlapEPV realisedPV expect ActuarialJointD.expect
  simp only [← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  unfold totalInstalment replacementTotalInstalment replacementPayment
  split_ifs <;> grind
