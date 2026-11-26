-- Prove2me | solution 1 for PascalMinusOne.mixed_eq_sum_two_powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:32.3308+00:00
-- url     : https://prove2.me/submissions/e8ce01ae-70ec-4785-af9d-268fdce75e11

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_parityDigitSums_add_eq_sum
import Theorems.Thm_PascalMinusOne_digitAt_le_parityDigitSum
import Theorems.Thm_PascalMinusOne_exists_ofDigits_eq_pow_of_sum_eq_one
import Theorems.Thm_PascalMinusOne_not_dvd_add_same_parity_powers
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
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hmN : m ∣ N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ s t, s < t ∧ N = p ^ s + p ^ t ∧ ¬ (Even s ↔ Even t) := by
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hNne : N ≠ 0 := by
    intro hN
    subst N
    simp at hmixed
  let t := Nat.log p N
  let L := Nat.digits p N
  have hpowle : p ^ t ≤ N := by
    dsimp [t]
    exact Nat.pow_log_le_self p hNne
  have hNlt : N < p ^ (t + 1) := by
    dsimp [t]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp1 N
  have hqone : 1 ≤ N / p ^ t := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp0 t)]
    simpa using hpowle
  have hqpos : 0 < N / p ^ t := by omega
  have hqlt : N / p ^ t < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
    simpa [pow_succ, Nat.mul_comm] using hNlt
  have htocc : Occupied p N t := by
    dsimp [Occupied, digitAt]
    rw [Nat.mod_eq_of_lt hqlt]
    exact hqpos
  have htdigit : digitAt p N t = 1 := by
    have hbound :=
      digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
    by_cases htEven : Even t
    · rw [if_pos htEven, hmixed.1] at hbound
      have htpos : 0 < digitAt p N t := htocc
      omega
    · rw [if_neg htEven, hmixed.2] at hbound
      have htpos : 0 < digitAt p N t := htocc
      omega
  have hqeq : N / p ^ t = 1 := by
    have h := htdigit
    dsimp [digitAt] at h
    rw [Nat.mod_eq_of_lt hqlt] at h
    exact h
  have hLlen : L.length = t + 1 := by
    dsimp [L, t]
    exact Nat.length_digits p N hp1 hNne
  have htlen : t < L.length := by omega
  have hLsum : L.sum = 2 := by
    have hsum :
        evenDigitSum p N + oddDigitSum p N = L.sum := by
      simpa [L, evenDigitSum, oddDigitSum] using
        parityDigitSums_add_eq_sum L
    omega
  have hgettop : L.getD t 0 = digitAt p N t := by
    dsimp [L]
    rw [Nat.getD_digits N t hp2]
    rfl
  have hdrop : L.drop t = [L.getD t 0] := by
    rw [List.drop_eq_getElem_cons htlen,
      ← List.getD_eq_getElem L 0 htlen,
      ← hLlen, List.drop_length]
  have hdecomp : (L.take t).sum + digitAt p N t = 2 := by
    have h := List.sum_take_add_sum_drop L t
    rw [hdrop, List.sum_singleton, hgettop, hLsum] at h
    exact h
  have hprefsum : (L.take t).sum = 1 := by
    omega
  have htakeLen : (L.take t).length = t := by
    exact List.length_take_of_le htlen.le
  obtain ⟨s, hslen, hprefixpow⟩ :=
    exists_ofDigits_eq_pow_of_sum_eq_one p (L.take t) hprefsum
  have hst : s < t := by
    rw [htakeLen] at hslen
    exact hslen
  have hmod : N % p ^ t = p ^ s := by
    rw [Nat.self_mod_pow_eq_ofDigits_take t N hp2]
    simpa [L] using hprefixpow
  have hNpow : N = p ^ s + p ^ t := by
    calc
      N = N % p ^ t + p ^ t * (N / p ^ t) :=
        (Nat.mod_add_div N (p ^ t)).symm
      _ = p ^ s + p ^ t := by rw [hmod, hqeq]; simp
  have hopposite : ¬ (Even s ↔ Even t) := by
    intro hsame
    have hbad :=
      not_dvd_add_same_parity_powers
        (m := m) (p := p) (a := 1) (b := 1) (u := s) (v := t)
        hm hpm (by omega) (by omega) hsame
    apply hbad
    rw [one_mul, one_mul, ← hNpow]
    exact hmN
  exact ⟨s, t, hst, hNpow, hopposite⟩
end PascalMinusOne
