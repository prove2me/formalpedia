-- Prove2me | solution 1 for ThreeSum.LightTernaryRowSelector.pick_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:59.70823+00:00
-- url     : https://prove2.me/submissions/1ff4add8-029e-44eb-a95b-963c606e8f9f

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
theorem _root_.solution (good : ℕ → Prop) [DecidablePred good] (n : ℕ) :
    0 < pick good n ↔ ∃ i < n, good i := by
  induction n with
  | zero => simp [pick]
  | succ n ih =>
    rw [pick]
    split_ifs with hn
    · constructor
      · intro h; exact ⟨n,by omega,hn⟩
      · intro h; omega
    · rw [ih]
      constructor
      · rintro ⟨i,hi,hg⟩; exact ⟨i,by omega,hg⟩
      · rintro ⟨i,hi,hg⟩
        refine ⟨i, ?_,hg⟩
        by_contra h
        have : i=n := by omega
        exact hn (this ▸ hg)
end ThreeSum.LightTernaryRowSelector
