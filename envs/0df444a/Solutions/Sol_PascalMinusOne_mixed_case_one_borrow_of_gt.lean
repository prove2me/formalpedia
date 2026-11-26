-- Prove2me | solution 1 for PascalMinusOne.mixed_case_one_borrow_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:34.330982+00:00
-- url     : https://prove2.me/submissions/45448516-d1ce-4c85-94ab-a78470803e94

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_parityDigitSums_add_eq_sum
import Theorems.Thm_PascalMinusOne_digitAt_le_parityDigitSum
import Theorems.Thm_PascalMinusOne_ofDigits_le_pow_length_pred_of_sum_eq_one
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
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
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
  have ht1 : 1 ≤ t := by
    by_contra htNotPos
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos htNotPos
    simp [ht0] at hprefsum
  have htakeLen : (L.take t).length = t := by
    exact List.length_take_of_le htlen.le
  have hNmodle : N % p ^ t ≤ p ^ (t - 1) := by
    rw [Nat.self_mod_pow_eq_ofDigits_take t N hp2]
    have hbound :=
      ofDigits_le_pow_length_pred_of_sum_eq_one (p := p) hp0 (L.take t) hprefsum
    rw [htakeLen] at hbound
    exact hbound
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
  have hpowpred_lt_k : p ^ (t - 1) < k := by
    dsimp [k]
    have hm1 : 1 < m := by omega
    calc
      p ^ (t - 1) = 1 * p ^ (t - 1) := by simp
      _ < m * p ^ (t - 1) :=
        (Nat.mul_lt_mul_right hpowpredpos).2 hm1
  have hcarry : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow] at hprefix
    exact (Nat.not_le_of_gt (hNmodle.trans_lt hpowpred_lt_k)) hprefix
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
