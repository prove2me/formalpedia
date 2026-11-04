-- Prove2me | solution 1 for ThreeSum.LightTernaryRowSelector.pick_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:58.509202+00:00
-- url     : https://prove2.me/submissions/f0a53f72-ce52-426c-8e3b-71091b2ab957

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
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
open ThreeSum ThreeSum.LightTernaryRowSelector
open Light
namespace ThreeSum.LightTernaryRowSelector
theorem _root_.solution (good : ℕ → Prop) [DecidablePred good] (n : ℕ) : pick good n ≤ n := by
  induction n with
  | zero => simp [pick]
  | succ n ih => simp only [pick]; split_ifs <;> omega
end ThreeSum.LightTernaryRowSelector
