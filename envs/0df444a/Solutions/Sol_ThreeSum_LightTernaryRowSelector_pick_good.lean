-- Prove2me | solution 1 for ThreeSum.LightTernaryRowSelector.pick_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:42.263197+00:00
-- url     : https://prove2.me/submissions/06258546-5068-4cfe-aa25-fa2bf081872b

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
theorem _root_.solution (good : ℕ → Prop) [DecidablePred good] (n : ℕ) (h : 0 < pick good n) :
    good (pick good n-1) := by
  induction n with
  | zero => simp [pick] at h
  | succ n ih =>
    rw [pick] at h ⊢
    split_ifs at h ⊢ with hn
    · simpa using hn
    · exact ih h
end ThreeSum.LightTernaryRowSelector
