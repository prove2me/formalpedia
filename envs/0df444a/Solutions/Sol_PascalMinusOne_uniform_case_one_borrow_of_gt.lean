-- Prove2me | solution 1 for PascalMinusOne.uniform_case_one_borrow_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:32.955647+00:00
-- url     : https://prove2.me/submissions/67be2f4b-5f8b-4464-89c1-76dcd359b4aa

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_digitAt_le_parityDigitSum
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_mod_pow_succ_eq_mod_add_digitAt
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
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p) (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hNpos : 0 < N := by omega
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  let t := Nat.log p N
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
  have htocc : 0 < digitAt p N t := by
    rw [digitAt, Nat.mod_eq_of_lt hqlt]
    exact hqpos
  have htdata : 1 ≤ t ∧ digitAt p N (t - 1) = 0 := by
    rcases huniform with hevenUniform | hoddUniform
    · rcases hevenUniform with ⟨heven, hodd⟩
      have htEven : Even t := by
        by_contra htNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_neg htNotEven, hodd] at hbound
        omega
      have htpos : 0 < t := by
        by_contra htNotPos
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos htNotPos
        have hNP : N < p := by
          simpa [ht0] using hNlt
        have hdigit0 : digitAt p N 0 = N := by
          simp [digitAt, Nat.mod_eq_of_lt hNP]
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := 0) hp2
        have hNle : N ≤ m := by
          simpa [hdigit0, heven] using hbound
        omega
      have ht1 : 1 ≤ t := by omega
      have hpredNotEven : ¬ Even (t - 1) := by
        have h := htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one] at h
        exact h
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_neg hpredNotEven, hodd] at hbound
      exact ⟨ht1, by omega⟩
    · rcases hoddUniform with ⟨heven, hodd⟩
      have htNotEven : ¬ Even t := by
        intro htEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_pos htEven, heven] at hbound
        omega
      have htpos : 0 < t := by
        by_contra htNotPos
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos htNotPos
        apply htNotEven
        simp [ht0]
      have ht1 : 1 ≤ t := by omega
      have hpredEven : Even (t - 1) := by
        by_contra hpredNotEven
        apply htNotEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one]
        exact hpredNotEven
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_pos hpredEven, heven] at hbound
      exact ⟨ht1, by omega⟩
  rcases htdata with ⟨ht1, hpredzero⟩
  have hNmod : N % p ^ t = N % p ^ (t - 1) := by
    have h := mod_pow_succ_eq_mod_add_digitAt p N (t - 1)
    rw [Nat.sub_add_cancel ht1] at h
    simpa [hpredzero] using h
  have hNmodlt : N % p ^ t < p ^ (t - 1) := by
    rw [hNmod]
    exact Nat.mod_lt _ (pow_pos hp0 _)
  let k := m * p ^ (t - 1)
  have hpowpredpos : 0 < p ^ (t - 1) := pow_pos hp0 _
  have hkpos : 0 < k := by
    dsimp [k]
    exact Nat.mul_pos (by omega) hpowpredpos
  have hkltpow : k < p ^ t := by
    have hmul : m * p ^ (t - 1) < p * p ^ (t - 1) :=
      (Nat.mul_lt_mul_right hpowpredpos).2 hpmgt
    dsimp [k]
    calc
      m * p ^ (t - 1) < p * p ^ (t - 1) := hmul
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel ht1]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    dsimp [k]
    exact dvd_mul_right m _
  have hnocarry_of_lt {j : ℕ} (hjt : j < t) : ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    have hjle : j ≤ t - 1 := by omega
    have hdvd : p ^ j ∣ k := by
      dsimp [k]
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow p hjle) m
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    exact Nat.zero_le _
  have hpowpred_le_k : p ^ (t - 1) ≤ k := by
    dsimp [k]
    have hm1 : 1 ≤ m := by omega
    calc
      p ^ (t - 1) = 1 * p ^ (t - 1) := by simp
      _ ≤ m * p ^ (t - 1) := by
        exact Nat.mul_le_mul_right _ hm1
  have hcarry : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow] at hprefix
    exact (Nat.not_le_of_gt (hNmodlt.trans_le hpowpred_le_k)) hprefix
  have hfilter :
      ((Finset.Ico 1 (t + 1)).filter fun i ↦ CarryAt p N k i) = {t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hj1, hjlt⟩, hjcarry⟩
      have hjle : j ≤ t := Nat.lt_succ_iff.mp hjlt
      by_cases hjt : j = t
      · exact hjt
      · have hjlt' : j < t := by omega
        exact (hnocarry_of_lt hjlt' hjcarry).elim
    · intro hj
      subst j
      exact ⟨⟨ht1, Nat.lt_succ_self t⟩, hcarry⟩
  have hcount : carryCount p N k (t + 1) = 1 := by
    rw [carryCount, hfilter]
    simp
  have hval : padicValNat p (N.choose k) = 1 := by
    rw [padicVal_choose_eq_carryCount hkn (Nat.lt_succ_self t), hcount]
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval⟩
end PascalMinusOne
