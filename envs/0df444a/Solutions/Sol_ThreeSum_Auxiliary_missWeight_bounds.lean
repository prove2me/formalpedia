-- Prove2me | solution 1 for ThreeSum.Auxiliary.missWeight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:56.594393+00:00
-- url     : https://prove2.me/submissions/ac8bf8c5-f549-4c78-8af2-ea6dcd250fcf

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
import Theorems.Thm_ThreeSum_Auxiliary_moduli_card
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) (z : ℤ) :
    Arithmetic.missWeight (moduli C) z ≤ C.card := by
  unfold Arithmetic.missWeight
  calc
    _ ≤ ∑ _p ∈ moduli C, 1 := by
      apply sum_le_sum
      intro p hp
      split <;> omega
    _ = C.card := by simp [moduli_card]
end ThreeSum.Auxiliary
