-- Prove2me | solution 1 for ThreeSum.LightPairSearch.goodCode_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:46.243663+00:00
-- url     : https://prove2.me/submissions/f34f9810-914a-49d9-a701-1f9bf7c4f9ad

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
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
open ThreeSum ThreeSum.LightPairSearch
set_option maxHeartbeats 300000
namespace ThreeSum.LightPairSearch
theorem _root_.solution (q u v : ℕ) (hq : 0<q) (hv : v<q)
    (good : ℕ → ℕ → Prop) : goodCode q good (u*q+v) ↔ good u v := by
  have hdiv : (u*q+v)/q=u := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt hv,Nat.zero_add]
  have hmod : (u*q+v)%q=v := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hv]
  simp only [goodCode,hdiv,hmod]
end ThreeSum.LightPairSearch
