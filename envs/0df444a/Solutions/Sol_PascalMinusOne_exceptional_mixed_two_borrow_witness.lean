-- Prove2me | solution 1 for PascalMinusOne.exceptional_mixed_two_borrow_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:24:20.381794+00:00
-- url     : https://prove2.me/submissions/7b1ac78c-f291-4d0d-b2ca-67428de7279f

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_mixed_eq_sum_two_powers
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_not_carryAt_iff_mod_pow_le
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_padicVal_choose_eq_carryCount
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
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hpmMod : p % m = m - 1 := by
    rw [hpm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpSucc : p + 1 = m := by omega
  obtain ⟨s, t, hst, hNpow, hopposite⟩ :=
    mixed_eq_sum_two_powers hm hp hpmMod hmN hmixed
  have ht2 : 2 ≤ t := by
    by_contra htNot
    have htlt : t < 2 := Nat.lt_of_not_ge htNot
    have hs0 : s = 0 := by omega
    have ht1 : t = 1 := by omega
    have hNeq : N = m := by
      rw [hNpow, hs0, ht1, pow_zero, pow_one]
      omega
    omega
  have hgap : s = t - 1 ∨ s < t - 2 := by
    by_cases hsPred : s = t - 1
    · exact Or.inl hsPred
    · right
      have hsne : s ≠ t - 2 := by
        intro hsEq
        apply hopposite
        have htEq : t = s + 2 := by omega
        rw [htEq, Nat.even_add']
        have hnotOddTwo : ¬ Odd (2 : ℕ) := by
          norm_num [Odd]
        simp [hnotOddTwo, Nat.not_odd_iff_even]
      omega
  have hpowst : p ^ s < p ^ t :=
    Nat.pow_lt_pow_right hp1 hst
  have hpowle : p ^ t ≤ N := by
    rw [hNpow]
    omega
  have hNlt2 : N < 2 * p ^ t := by
    rw [hNpow]
    omega
  have hNltTop : N < p ^ (t + 1) := by
    calc
      N < 2 * p ^ t := hNlt2
      _ ≤ p * p ^ t := Nat.mul_le_mul_right (p ^ t) hp2
      _ = p ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  have hlog : Nat.log p N = t :=
    Nat.log_eq_of_pow_le_of_lt_pow hpowle hNltTop
  have hpowPred :
      p ^ (t - 2) < p ^ (t - 1) :=
    Nat.pow_lt_pow_right hp1 (by omega)
  let k := p ^ (t - 1) + p ^ (t - 2)
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hkltpow : k < p ^ t := by
    have hlt2 :
        p ^ (t - 1) + p ^ (t - 2) < 2 * p ^ (t - 1) := by
      omega
    dsimp [k]
    calc
      p ^ (t - 1) + p ^ (t - 2) < 2 * p ^ (t - 1) := hlt2
      _ ≤ p * p ^ (t - 1) := Nat.mul_le_mul_right (p ^ (t - 1)) hp2
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel (by omega)]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    refine ⟨p ^ (t - 2), ?_⟩
    dsimp [k]
    have htSub : t - 2 + 1 = t - 1 := by omega
    calc
      p ^ (t - 1) + p ^ (t - 2) =
          p ^ (t - 2) * p + p ^ (t - 2) := by
            rw [← pow_succ, htSub]
      _ = (p + 1) * p ^ (t - 2) := by ring
      _ = m * p ^ (t - 2) := by rw [hpSucc]
  have hnocarry_of_lt {j : ℕ} (hjt : j < t - 1) :
      ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    have hj2 : j ≤ t - 2 := by omega
    have hj1 : j ≤ t - 1 := by omega
    have hdvd : p ^ j ∣ k := by
      dsimp [k]
      exact dvd_add
        (Nat.pow_dvd_pow p hj1)
        (Nat.pow_dvd_pow p hj2)
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    exact Nat.zero_le _
  have hkmodPred : k % p ^ (t - 1) = p ^ (t - 2) := by
    dsimp [k]
    rw [Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt hpowPred]
    simpa using Nat.mod_eq_of_lt hpowPred
  have hNmodPredLt : N % p ^ (t - 1) < p ^ (t - 2) := by
    rcases hgap with hsPred | hsLow
    · have htopdvd : p ^ (t - 1) ∣ p ^ t :=
        Nat.pow_dvd_pow p (by omega)
      rw [hNpow, hsPred, Nat.add_mod, Nat.mod_self,
        Nat.mod_eq_zero_of_dvd htopdvd]
      simpa using pow_pos hp0 (t - 2)
    · have hsPredLt : s < t - 1 := by omega
      have hsPowLt : p ^ s < p ^ (t - 2) :=
        Nat.pow_lt_pow_right hp1 hsLow
      have htopdvd : p ^ (t - 1) ∣ p ^ t :=
        Nat.pow_dvd_pow p (by omega)
      rw [hNpow, Nat.add_mod,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsPredLt),
        Nat.mod_eq_zero_of_dvd htopdvd]
      simpa [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsPredLt)] using hsPowLt
  have hcarryPred : CarryAt p N k (t - 1) := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t - 1) hp0 hkn).1 hnocarry
    rw [hkmodPred] at hprefix
    omega
  have hNmodTop : N % p ^ t = p ^ s := by
    rw [hNpow, Nat.add_mod, Nat.mod_eq_of_lt hpowst, Nat.mod_self]
    simpa using Nat.mod_eq_of_lt hpowst
  have hpowSltK : p ^ s < k := by
    dsimp [k]
    by_cases hsPred : s = t - 1
    · rw [hsPred]
      have hpowLowPos : 0 < p ^ (t - 2) := pow_pos hp0 _
      omega
    · have hsLow : s < t - 1 := by omega
      have hpowLow : p ^ s < p ^ (t - 1) :=
        Nat.pow_lt_pow_right hp1 hsLow
      omega
  have hcarryTop : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow, hNmodTop] at hprefix
    exact (Nat.not_le_of_gt hpowSltK) hprefix
  have hfilter :
      ((Finset.Ico 1 (t + 1)).filter fun i ↦ CarryAt p N k i) =
        {t - 1, t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hj1, hjlt⟩, hjcarry⟩
      by_cases hjTop : j = t
      · exact Or.inr hjTop
      by_cases hjPred : j = t - 1
      · exact Or.inl hjPred
      have hjltPred : j < t - 1 := by omega
      exact (hnocarry_of_lt hjltPred hjcarry).elim
    · intro hj
      rcases hj with hjPred | hjTop
      · subst j
        exact ⟨⟨by omega, by omega⟩, hcarryPred⟩
      · subst j
        exact ⟨⟨by omega, Nat.lt_succ_self t⟩, hcarryTop⟩
  have hcount : carryCount p N k (t + 1) = 2 := by
    rw [carryCount, hfilter]
    have hne : t - 1 ≠ t := by omega
    simp [hne]
  have hloglt : Nat.log p N < t + 1 := by
    rw [hlog]
    exact Nat.lt_succ_self t
  have hval : padicValNat p (N.choose k) = 2 := by
    rw [padicVal_choose_eq_carryCount hkn hloglt, hcount]
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval⟩
end PascalMinusOne
