-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomial_coeff_binaryDegree_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/e1a90707-cf4e-4352-92be-2a4fcf4673a2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_coeff_binaryDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).coeff (matchingBinaryDegree P) ≠ 0 := by
  rw [matchingPolynomial_coeff_binaryDegree]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero P.card))
end PermanentFormulaLowerBound
