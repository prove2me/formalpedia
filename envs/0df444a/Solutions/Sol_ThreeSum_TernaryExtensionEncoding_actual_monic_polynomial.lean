-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.actual_monic_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:24.562074+00:00
-- url     : https://prove2.me/submissions/d2ea51c1-e2a2-4cde-b118-b0b9e8c9e662

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicVector_polynomial
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_monic_code
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_as_vector

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d code : ℕ} (hc : code<p^d) :
    arrayPolynomial (p := p) (d+1) (fun k => (code+p^d)/p^k%p)=monicOfCode d code := by
  rw [arrayPolynomial_as_vector]
  change vectorPolynomial (coefficientVector (d+1) (code+p^d))=monicOfCode d code
  rw [decode_monic_code hc,monicVector_polynomial]
  rfl
end ThreeSum.TernaryExtensionEncoding
