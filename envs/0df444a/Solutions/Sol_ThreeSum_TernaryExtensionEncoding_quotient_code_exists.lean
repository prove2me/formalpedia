-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.quotient_code_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:08.105391+00:00
-- url     : https://prove2.me/submissions/3fe721c5-d727-4645-ac9f-00b4dfd3b710

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_digits
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_check_iff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_remainderRelation_exists


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) {c : ℕ} (hc : c<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f) (x y : ℕ) :
    ∃ h<p^f.natDegree, ∃ r<p^f.natDegree,
      LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
        (LightPolynomialQuotientCheck.expected p f.natDegree (codeDigits (p := p) h)
          (codeDigits (p := p) (c+p^f.natDegree)) (codeDigits (p := p) r))
        f.natDegree f.natDegree (2*f.natDegree) := by
  obtain ⟨h,r,hr⟩ := remainderRelation_exists hf hd
    (coefficientVector f.natDegree x) (coefficientVector f.natDegree y)
  refine ⟨coefficientCode h,coefficientCode_lt h,coefficientCode r,coefficientCode_lt r,?_⟩
  apply (quotient_check_iff hc (coefficientCode_lt r) _ _).mpr
  rw [arrayPolynomial_digits,arrayPolynomial_digits,coefficientVector_code,
    coefficientVector_code,hm]
  exact hr
end ThreeSum.TernaryExtensionEncoding
