-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicVector_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:44.212198+00:00
-- url     : https://prove2.me/submissions/20c2acd5-4a75-4305-8bf4-bc7ad58eb4d0

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
    coefficientCode (monicVector a)=coefficientCode a+p^d := by
  unfold coefficientCode
  rw [List.ofFn_succ_last]
  simp [monicVector,Nat.ofDigits_append,ZMod.val_one,
    Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]
end ThreeSum.TernaryExtensionEncoding
