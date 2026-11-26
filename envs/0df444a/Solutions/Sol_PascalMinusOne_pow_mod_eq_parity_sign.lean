-- Prove2me | solution 1 for PascalMinusOne.pow_mod_eq_parity_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:19:35.648957+00:00
-- url     : https://prove2.me/submissions/029a5961-5014-4718-a7d7-837918a5bec0

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_m
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_zero_m



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {m p i : ℕ} (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    p ^ i % m = if Even i then 1 else m - 1 := by
  have hpmod : p ≡ m - 1 [MOD m] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    exact hpm
  have hsq : (m - 1) ^ 2 ≡ 1 [MOD m] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < m)]
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have hm2 : m - 2 + 2 = m := Nat.sub_add_cancel hm
    have heq : (m - 1) ^ 2 = m * (m - 2) + 1 := by
      nlinarith
    rw [heq]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (by omega : 1 < m)]
  by_cases hi : Even i
  · rw [if_pos hi]
    obtain ⟨j, rfl⟩ := hi
    have hpow : p ^ (j + j) ≡ 1 [MOD m] := by
      calc
        p ^ (j + j) ≡ (m - 1) ^ (j + j) [MOD m] := hpmod.pow _
        _ = ((m - 1) ^ 2) ^ j := by rw [← two_mul j, pow_mul]
        _ ≡ 1 ^ j [MOD m] := hsq.pow j
        _ = 1 := by simp
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < m)] using hpow
  · rw [if_neg hi]
    have hodd : Odd i := Nat.not_even_iff_odd.mp hi
    obtain ⟨j, rfl⟩ := hodd
    have hpow : p ^ (2 * j + 1) ≡ m - 1 [MOD m] := by
      calc
        p ^ (2 * j + 1) ≡ (m - 1) ^ (2 * j + 1) [MOD m] := hpmod.pow _
        _ = ((m - 1) ^ 2) ^ j * (m - 1) := by
          rw [pow_add, pow_one, pow_mul]
        _ ≡ 1 ^ j * (m - 1) [MOD m] := (hsq.pow j).mul Nat.ModEq.rfl
        _ = m - 1 := by simp
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : m - 1 < m)] using hpow
end PascalMinusOne
