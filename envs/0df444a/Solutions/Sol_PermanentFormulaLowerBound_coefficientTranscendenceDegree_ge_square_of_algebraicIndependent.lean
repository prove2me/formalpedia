-- Prove2me | solution 1 for PermanentFormulaLowerBound.coefficientTranscendenceDegree_ge_square_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/cd7a60e0-c5f5-40bd-9076-76d055eceac8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_coefficientTranscendenceDegree_ge_of_algebraicIndependent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {Y Z F : Type*} [Field F] {m : ℕ}
    (p : MvPolynomial (Y ⊕ Z) F)
    (α : Fin m × Fin m → Y →₀ ℕ)
    (hind : AlgebraicIndependent F
      (fun de => coefficientPolynomial p (α de))) :
    ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree p := by
  simpa using
    coefficientTranscendenceDegree_ge_of_algebraicIndependent p α hind
end PermanentFormulaLowerBound
