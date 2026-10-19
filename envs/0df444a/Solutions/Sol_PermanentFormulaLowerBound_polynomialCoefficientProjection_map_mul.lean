-- Prove2me | solution 1 for PermanentFormulaLowerBound.polynomialCoefficientProjection_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/b1ee09a9-a672-470a-a07d-e85ab96ac3ce

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
    (φ : E →ₗ[K] K) (q : MvPolynomial ι K) (f : MvPolynomial ι E) :
    polynomialCoefficientProjection φ
        (MvPolynomial.map (algebraMap K E) q * f) =
      q * polynomialCoefficientProjection φ f := by
  classical
  apply MvPolynomial.ext
  intro s
  have hcoeff (g : MvPolynomial ι E) (index : ι →₀ ℕ) :
      MvPolynomial.coeff index (polynomialCoefficientProjection φ g) =
        φ (MvPolynomial.coeff index g) := rfl
  simp only [hcoeff, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simpa [Algebra.smul_def] using
    φ.map_smul (MvPolynomial.coeff a.1 q) (MvPolynomial.coeff a.2 f)
end PermanentFormulaLowerBound
