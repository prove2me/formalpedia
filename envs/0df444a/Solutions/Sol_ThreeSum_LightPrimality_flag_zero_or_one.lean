-- Prove2me | solution 1 for ThreeSum.LightPrimality.flag_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:28.281272+00:00
-- url     : https://prove2.me/submissions/d428a52b-863f-4dab-b8b6-fd1f62d7978f

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
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
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimality
theorem _root_.solution (n i : ℕ) : flag n i = 0 ∨ flag n i = 1 := by
  induction i with
  | zero => simp [flag]
  | succ i ih =>
      unfold flag
      split
      · exact Or.inl rfl
      · exact ih
end ThreeSum.LightPrimality
