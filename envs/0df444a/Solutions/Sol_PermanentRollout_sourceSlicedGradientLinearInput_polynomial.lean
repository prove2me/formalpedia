-- Prove2me | solution 1 for PermanentRollout.sourceSlicedGradientLinearInput_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/d4c9cff4-06e3-480d-8174-5191e05a0d25

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (j : Fin m) :
    (sourceSlicedGradientLinearInput W j).polynomial =
      linearCoordinatePolynomial W j := by
  simp only [FreeAffineInput.polynomial,
    sourceSlicedGradientLinearInput, MvPolynomial.C_0, zero_add,
    Finsupp.linearCombination_eq_fintype_linearCombination_apply,
    Fintype.linearCombination_apply, linearCoordinatePolynomial]
  apply Finset.sum_congr rfl
  intro i _
  simp [MvPolynomial.smul_eq_C_mul]
end PermanentRollout
