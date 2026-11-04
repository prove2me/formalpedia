-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.factor_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:43.195201+00:00
-- url     : https://prove2.me/submissions/e27c0a84-5119-4cd1-853f-dd1211b09c35

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_codeDigits_lt
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_actual_monic_polynomial_padded
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_actual_monic_polynomial
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_product_valid_iff_polynomial


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d e c u v : ℕ} (hd : 0<d) (he : e<d)
    (hc : c<p^d) (hu : u<p^e) (hv : v<p^(d-e)) :
    LightPolynomialProductCheck.Valid p (codeDigits (p := p) (u+p^e))
      (codeDigits (p := p) (v+p^(d-e))) (codeDigits (p := p) (c+p^d)) (e+1) (d-e+1) (2*d) ↔
    monicOfCode (p := p) e u*monicOfCode (d-e) v=monicOfCode d c := by
  have hmu : arrayPolynomial (p := p) (e+1) (codeDigits (p := p) (u+p^e))=monicOfCode e u :=
    actual_monic_polynomial hu
  have hmv : arrayPolynomial (p := p) (d-e+1) (codeDigits (p := p) (v+p^(d-e)))=monicOfCode (d-e) v :=
    actual_monic_polynomial hv
  rw [product_valid_iff_polynomial _ _ _ (e+1) (d-e+1) (2*d) (by omega)
    (fun k hk => codeDigits_lt _ _),hmu,hmv,actual_monic_polynomial_padded hd hc]
end ThreeSum.TernaryExtensionEncoding
