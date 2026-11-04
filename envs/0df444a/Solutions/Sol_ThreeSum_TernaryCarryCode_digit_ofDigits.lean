-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.digit_ofDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:30.425616+00:00
-- url     : https://prove2.me/submissions/1db15562-85dd-4221-833d-9965c0a10de9

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog


namespace ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
private theorem head_drop (l : List ℕ) (j : ℕ) : (l.drop j).head! = l.getD j 0 := by
  induction l generalizing j with
  | nil => cases j <;> simp
  | cons a l ih => cases j with
    | zero => simp
    | succ j => simpa using ih j
end ThreeSum.TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution {b : ℕ} (hb : 1<b) (l : List ℕ)
    (hl : ∀ x∈l, x<b) (j : ℕ) :
    digit b (Nat.ofDigits b l) j=l.getD j 0 := by
  unfold digit quotient
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop j (by omega) l hl,
    Nat.ofDigits_mod_eq_head!,head_drop]
  have hget : l.getD j 0<b := by
    by_cases hj : j<l.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hl _ (List.getElem_mem _)
    · rw [List.getD_eq_default l 0 (by omega)]
      omega
  exact Nat.mod_eq_of_lt hget
end ThreeSum.TernaryCarryCode
