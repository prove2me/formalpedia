-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicVector_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:45.364482+00:00
-- url     : https://prove2.me/submissions/14272cf2-c1fb-4633-b260-cefb145d72a3

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) :
    vectorPolynomial (monicVector a)=monicCandidate a := by
  unfold vectorPolynomial monicCandidate
  rw [Fin.sum_univ_castSucc]
  simp [monicVector,vectorPolynomial,monomial_one_right_eq_X_pow,add_comm]
end ThreeSum.TernaryExtensionEncoding
