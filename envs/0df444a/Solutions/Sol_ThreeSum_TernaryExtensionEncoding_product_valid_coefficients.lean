-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.product_valid_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:43.019058+00:00
-- url     : https://prove2.me/submissions/9f11c1ba-ad02-4d31-ac3a-4f8fbfe1e75e

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_product_coeff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (a b expected : ℕ → ℕ) (n m len : ℕ)
    (h : LightPolynomialProductCheck.Valid p a b expected n m len) :
    ∀ k<len, (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=
      (expected k : ZMod p) := by
  intro k hk
  rw [arrayPolynomial_product_coeff]
  have hh := h k hk
  change expected k=LightPolynomialCoefficient.coefficient p a b n m k at hh
  exact congrArg (fun z : ℕ => (z : ZMod p)) hh.symm
end ThreeSum.TernaryExtensionEncoding
