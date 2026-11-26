-- Prove2me | solution 1 for PascalMinusOne.digitwiseLE_iff_mod_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:01.074228+00:00
-- url     : https://prove2.me/submissions/27ca292a-53a7-4273-9478-461f1c16c1c6

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
import Theorems.Thm_PascalMinusOne_mod_pow_succ_eq_mod_add_digitAt
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {p k n : ℕ} (hp : 0 < p) :
    DigitwiseLE p k n ↔ ∀ i, k % p ^ i ≤ n % p ^ i := by
  constructor
  · intro hdigit i
    induction i with
    | zero =>
        simpa only [pow_zero, Nat.mod_one] using (Nat.le_refl 0)
    | succ i ih =>
        rw [mod_pow_succ_eq_mod_add_digitAt, mod_pow_succ_eq_mod_add_digitAt]
        exact Nat.add_le_add ih (Nat.mul_le_mul_left _ (hdigit i))
  · intro hprefix i
    have hnext := hprefix (i + 1)
    rw [mod_pow_succ_eq_mod_add_digitAt, mod_pow_succ_eq_mod_add_digitAt] at hnext
    by_contra hdigit
    have hlt : digitAt p n i < digitAt p k i := Nat.lt_of_not_ge hdigit
    have hpow : 0 < p ^ i := pow_pos hp i
    have hnmod : n % p ^ i < p ^ i := Nat.mod_lt _ hpow
    have hstep :
        p ^ i * (digitAt p n i + 1) ≤ p ^ i * digitAt p k i :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hlt)
    have hnlt :
        n % p ^ i + p ^ i * digitAt p n i <
          p ^ i * (digitAt p n i + 1) := by
      calc
        n % p ^ i + p ^ i * digitAt p n i <
            p ^ i + p ^ i * digitAt p n i :=
          Nat.add_lt_add_right hnmod _
        _ = p ^ i * (digitAt p n i + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    have htotal :
        n % p ^ i + p ^ i * digitAt p n i <
          k % p ^ i + p ^ i * digitAt p k i :=
      hnlt.trans_le (hstep.trans (Nat.le_add_left _ _))
    exact (Nat.not_lt_of_ge hnext) htotal
end PascalMinusOne
