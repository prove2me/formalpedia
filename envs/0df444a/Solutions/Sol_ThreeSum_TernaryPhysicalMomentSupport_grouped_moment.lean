-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalMomentSupport.grouped_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:31.996059+00:00
-- url     : https://prove2.me/submissions/14787499-8e16-4395-924c-b5248a03db47

import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_values_injective
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_values_coverage

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalMomentSupport
theorem _root_.solution (mode mass : P → ℤ) (k : ℕ) :
    moment (values mode) (weights mode mass) k=∑ a, mass a*mode a^k := by
  classical
  unfold moment weights
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a ha
  obtain ⟨i,hi⟩ := values_coverage mode a
  rw [sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    have hn : mode a≠values mode j := by
      intro h
      apply hji
      exact values_injective mode (h.symm.trans hi.symm)
    simp [hn]
  · simp
end ThreeSum.TernaryPhysicalMomentSupport
