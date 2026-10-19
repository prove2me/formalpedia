-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomial_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/441f29e9-1192-4dd5-879c-74adedb34164

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_natDegree_le
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_coeff_binaryDegree_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [Field F] [CharZero F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).natDegree = matchingBinaryDegree P := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (matchingPolynomial_natDegree_le p P)
    (matchingPolynomial_coeff_binaryDegree_ne_zero p P)
end PermanentFormulaLowerBound
