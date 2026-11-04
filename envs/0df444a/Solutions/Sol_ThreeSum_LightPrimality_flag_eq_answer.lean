-- Prove2me | solution 1 for ThreeSum.LightPrimality.flag_eq_answer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:26.157141+00:00
-- url     : https://prove2.me/submissions/4b323010-8e4c-45ed-90a9-944bb55d7cb7

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
import Theorems.Thm_ThreeSum_LightPrimality_flag_zero_or_one
import Theorems.Thm_ThreeSum_LightPrimality_prime_iff_flag_eq_one
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
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) : flag n (n-2) = answer n := by
  by_cases hp : Nat.Prime n
  · simp [answer,hp,(prime_iff_flag_eq_one hn).mp hp]
  · have hne := mt (prime_iff_flag_eq_one hn).mpr hp
    have hf := flag_zero_or_one n (n-2)
    simp only [answer,if_neg hp]
    omega
end ThreeSum.LightPrimality
