-- Prove2me | solution 1 for ThreeSum.LightPolynomialCoefficient.raw_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:51.753991+00:00
-- url     : https://prove2.me/submissions/6a5c7c37-977d-4230-a308-9580925ed8f8

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
namespace ThreeSum.LightPolynomialCoefficient
theorem _root_.solution (f g : ℕ → ℕ) (m k : ℕ) : rawCoefficient f g 0 m k=0 := by
  simp [rawCoefficient]
end ThreeSum.LightPolynomialCoefficient
