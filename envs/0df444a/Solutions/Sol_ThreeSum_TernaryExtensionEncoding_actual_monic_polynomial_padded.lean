-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.actual_monic_polynomial_padded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:38.981199+00:00
-- url     : https://prove2.me/submissions/a4b02c79-cae5-46a1-a8f7-ec9d5d64ba4b

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monic_code_lt
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_actual_monic_polynomial
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_extend
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_code_high_digit_zero


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d code : ℕ} (hd : 0<d) (hc : code<p^d) :
    arrayPolynomial (p := p) (2*d) (codeDigits (p := p) (code+p^d))=monicOfCode d code := by
  rw [arrayPolynomial_extend (d+1) (2*d) _ (by omega)]
  · exact actual_monic_polynomial hc
  · intro k hk
    exact code_high_digit_zero (monic_code_lt hc) hk
end ThreeSum.TernaryExtensionEncoding
