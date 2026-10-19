-- Prove2me | solution 1 for PermanentFormulaLowerBound.polynomialCoefficientProjection_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/92c60bfe-b9d8-4e59-8497-2ff12121fbe1

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
namespace PermanentFormulaLowerBound
theorem _root_.solution
    (φ : E →ₗ[K] K)
    (hφ : ∀ a : K, φ (algebraMap K E a) = a)
    (p : MvPolynomial ι K) :
    polynomialCoefficientProjection φ
        (MvPolynomial.map (algebraMap K E) p) = p := by
  apply MvPolynomial.ext
  intro s
  change
    φ (MvPolynomial.coeff s (MvPolynomial.map (algebraMap K E) p)) =
      MvPolynomial.coeff s p
  simpa [MvPolynomial.coeff_map] using hφ (MvPolynomial.coeff s p)
end PermanentFormulaLowerBound
