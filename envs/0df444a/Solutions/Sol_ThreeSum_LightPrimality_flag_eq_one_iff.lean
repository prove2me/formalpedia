-- Prove2me | solution 1 for ThreeSum.LightPrimality.flag_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:08.451456+00:00
-- url     : https://prove2.me/submissions/ed38f0c3-8d7f-4aa7-8245-0755213dae44

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
theorem _root_.solution (n i : ℕ) : flag n i = 1 ↔ ∀ j < i, ¬ j+2 ∣ n := by
  induction i with
  | zero => simp [flag]
  | succ i ih =>
      by_cases hd : i+2 ∣ n
      · simp only [flag,if_pos hd,zero_ne_one,false_iff]
        intro h
        exact h i (by omega) hd
      · rw [flag,if_neg hd,ih]
        constructor
        · intro h j hj
          by_cases hji : j < i
          · exact h j hji
          · have heq : j = i := by omega
            simpa only [heq] using hd
        · intro h j hj
          exact h j (by omega)
end ThreeSum.LightPrimality
