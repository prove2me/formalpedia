-- Prove2me | solution 1 for PascalMinusOne.not_dvd_add_same_parity_powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:33.082468+00:00
-- url     : https://prove2.me/submissions/919ef690-1e12-4aef-843b-25f559605954

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_pow_mod_eq_parity_sign
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
theorem _root_.solution
    {m p a b u v : ℕ} (hm : 3 ≤ m) (hpm : p % m = m - 1)
    (hpos : 0 < a + b) (hlt : a + b < m)
    (hpar : Even u ↔ Even v) :
    ¬ m ∣ a * p ^ u + b * p ^ v := by
  intro hdvd
  have hpu := pow_mod_eq_parity_sign (m := m) (p := p) (i := u) (by omega) hpm
  have hpv := pow_mod_eq_parity_sign (m := m) (p := p) (i := v) (by omega) hpm
  have hpuMod :
      p ^ u ≡ (if Even u then 1 else m - 1) [MOD m] := by
    rw [Nat.ModEq, hpu]
    by_cases hu : Even u
    · simp [hu, Nat.mod_eq_of_lt (by omega : 1 < m)]
    · simp [hu, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hpvMod :
      p ^ v ≡ (if Even v then 1 else m - 1) [MOD m] := by
    rw [Nat.ModEq, hpv]
    by_cases hv : Even v
    · simp [hv, Nat.mod_eq_of_lt (by omega : 1 < m)]
    · simp [hv, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hcomb :=
    (hpuMod.mul_left a).add (hpvMod.mul_left b)
  have hzero :
      a * p ^ u + b * p ^ v ≡ 0 [MOD m] :=
    hdvd.modEq_zero_nat
  have hrhs :=
    hcomb.symm.trans hzero
  have habdvd : m ∣ a + b := by
    by_cases hu : Even u
    · have hv : Even v := hpar.mp hu
      have hz : a + b ≡ 0 [MOD m] := by
        simpa [hu, hv] using hrhs
      exact Nat.modEq_zero_iff_dvd.mp hz
    · have hv : ¬ Even v := by
        intro hv
        exact hu (hpar.mpr hv)
      have hz :
          a * (m - 1) + b * (m - 1) ≡ 0 [MOD m] := by
        simpa [hu, hv] using hrhs
      have hprod : m ∣ (a + b) * (m - 1) := by
        rw [Nat.add_mul]
        exact Nat.modEq_zero_iff_dvd.mp hz
      have hcop : Nat.Coprime m (m - 1) := by
        rw [← Nat.coprime_sub_self_left (m := m - 1) (n := m) (by omega)]
        have hdiff : m - (m - 1) = 1 := by omega
        rw [hdiff]
        simp
      exact hcop.dvd_of_dvd_mul_right hprod
  have hmle : m ≤ a + b := Nat.le_of_dvd hpos habdvd
  omega
end PascalMinusOne
