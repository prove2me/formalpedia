-- Prove2me | solution 1 for ThreeSum.LightSupportMark.bit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:22.778519+00:00
-- url     : https://prove2.me/submissions/a45d34b4-53de-4dc4-95f0-71dee813b5a1

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
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
open ThreeSum ThreeSum.LightSupportMark
open Light Finset
namespace ThreeSum.LightSupportMark
theorem _root_.solution (key valid : ℕ → ℕ) (r : ℕ) : bit key valid r 0 = 0 := by
  simp [bit,Hit]
end ThreeSum.LightSupportMark
