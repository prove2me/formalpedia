-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.quotient_code_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:09.328462+00:00
-- url     : https://prove2.me/submissions/eede51b2-2892-4690-b38a-c65792468fbb

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_digits
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_code_coefficientVector
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_field_code
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_check_iff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_product_of_relation


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    {c x y h r : ℕ} (hc : c<p^f.natDegree) (hx : x<p^f.natDegree)
    (hy : y<p^f.natDegree) (hr : r<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f)
    (hg : LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
      (LightPolynomialQuotientCheck.expected p f.natDegree (codeDigits (p := p) h)
        (codeDigits (p := p) (c+p^f.natDegree)) (codeDigits (p := p) r))
      f.natDegree f.natDegree (2*f.natDegree)) :
    encode hf ((encodedEquiv hf).symm ⟨x,hx⟩*(encodedEquiv hf).symm ⟨y,hy⟩)=r := by
  have hg' := (quotient_check_iff hc hr _ _).mp hg
  rw [arrayPolynomial_digits,arrayPolynomial_digits,hm] at hg'
  have hrel : remainderRelation
      (coefficients hf ((encodedEquiv hf).symm ⟨x,hx⟩))
      (coefficients hf ((encodedEquiv hf).symm ⟨y,hy⟩))
      (coefficientVector f.natDegree h) (coefficientVector f.natDegree r) := by
    rw [decode_field_code,decode_field_code]
    exact hg'
  have hh := quotient_product_of_relation hf _ _ _ _ hrel
  have he := congrArg (coefficientCode (p := p)) hh
  rw [code_coefficientVector hr] at he
  exact he
end ThreeSum.TernaryExtensionEncoding
