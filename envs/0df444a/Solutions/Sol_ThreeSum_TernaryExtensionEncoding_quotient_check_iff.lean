-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.quotient_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:19.081528+00:00
-- url     : https://prove2.me/submissions/61308676-58ea-4c80-b007-299fd79dccaa

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_digits
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_actual_monic_polynomial
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_expected
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_code_high_digit_zero
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_product_valid_iff_polynomial


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d c h r : ℕ} (hc : c<p^d) (hr : r<p^d)
    (x y : ℕ → ℕ) :
    LightPolynomialProductCheck.Valid p x y
      (LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
        (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r)) d d (2*d) ↔
    arrayPolynomial d x*arrayPolynomial (p := p) d y=
      vectorPolynomial (coefficientVector d h)*monicOfCode d c+
        vectorPolynomial (coefficientVector d r) := by
  have hb : ∀ k<2*d, LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
      (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r) k<p := by
    intro k hk
    exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  rw [product_valid_iff_polynomial x y _ d d (2*d) (by omega) hb]
  have hz : ∀ k, d≤k → codeDigits (p := p) r k=0 := fun k hk => code_high_digit_zero hr hk
  have hm : arrayPolynomial (p := p) (d+1) (codeDigits (p := p) (c+p^d))=monicOfCode d c :=
    actual_monic_polynomial hc
  rw [arrayPolynomial_expected (p := p) d (codeDigits (p := p) h) (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r) hz,
    arrayPolynomial_digits,hm,arrayPolynomial_digits]
end ThreeSum.TernaryExtensionEncoding
