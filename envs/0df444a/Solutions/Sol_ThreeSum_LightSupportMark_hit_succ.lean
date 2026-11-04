-- Prove2me | solution 1 for ThreeSum.LightSupportMark.hit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:15.256737+00:00
-- url     : https://prove2.me/submissions/51540e46-cb49-4927-a4a7-a0771e3fd45b

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
theorem _root_.solution (key valid : ℕ → ℕ) (r i : ℕ) :
    Hit key valid r (i+1) ↔ Hit key valid r i ∨ (valid i=1 ∧ key i=r) := by
  simp only [Hit,mem_range]
  constructor
  · rintro ⟨j,hj,hv,hk⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact Or.inl ⟨j,hj,hv,hk⟩
    · exact Or.inr ⟨hv,hk⟩
  · rintro (⟨j,hj,hv,hk⟩ | ⟨hv,hk⟩)
    · exact ⟨j,by omega,hv,hk⟩
    · exact ⟨i,by omega,hv,hk⟩
end ThreeSum.LightSupportMark
