-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:37.482474+00:00
-- url     : https://prove2.me/submissions/7bfb9574-f793-4399-b2c1-cd685f3a7a27

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_as_vector


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (d code : ℕ) :
    arrayPolynomial (p := p) d (codeDigits (p := p) code)=vectorPolynomial (coefficientVector d code) := by
  rw [arrayPolynomial_as_vector]
  rfl
end ThreeSum.TernaryExtensionEncoding
