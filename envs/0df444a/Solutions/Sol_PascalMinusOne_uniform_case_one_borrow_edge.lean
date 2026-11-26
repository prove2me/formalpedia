-- Prove2me | solution 1 for PascalMinusOne.uniform_case_one_borrow_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:33.609908+00:00
-- url     : https://prove2.me/submissions/23d649bd-6bfd-4a12-a0c7-dc0b4ce25469

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_pow_mod_eq_parity_sign
import Theorems.Thm_PascalMinusOne_parityDigitSums_add_eq_sum
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
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ t s k,
      s < t ∧ Occupied p N t ∧ Occupied p N s ∧
      k = p ^ (t - 1) + p ^ s ∧
      Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm2 : 2 ≤ m := by omega
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hpmod : p % m = m - 1 := by
    rw [hpm, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hNpos : 0 < N := by omega
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
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
  have hLlen : L.length = t + 1 := by
    dsimp [L, t]
    exact Nat.length_digits p N hp1 hNne
  have htlen : t < L.length := by omega
  have hLsum : L.sum = m := by
    have hsum :
        evenDigitSum p N + oddDigitSum p N = L.sum := by
      simpa [L, evenDigitSum, oddDigitSum] using
        parityDigitSums_add_eq_sum L
    rcases huniform with h | h <;> omega
  have hgettop : L.getD t 0 = digitAt p N t := by
    dsimp [L]
    rw [Nat.getD_digits N t hp2]
    rfl
  have hdrop : L.drop t = [L.getD t 0] := by
    rw [List.drop_eq_getElem_cons htlen,
      ← List.getD_eq_getElem L 0 htlen,
      ← hLlen, List.drop_length]
  have hdecomp : (L.take t).sum + digitAt p N t = m := by
    have h := List.sum_take_add_sum_drop L t
    rw [hdrop, List.sum_singleton, hgettop, hLsum] at h
    exact h
  have htoplt : digitAt p N t < p := by
    simpa [digitAt] using Nat.mod_lt (N / p ^ t) hp0
  have hprefpos : 0 < (L.take t).sum := by
    omega
  obtain ⟨s, hsTake, hsposTake⟩ :=
    List.exists_mem_iff_getElem.mp
      (List.sum_pos_iff_exists_pos_nat.mp hprefpos)
  have htakeLen : (L.take t).length = t := by
    exact List.length_take_of_le htlen.le
  have hst : s < t := by
    rw [htakeLen] at hsTake
    exact hsTake
  have hslen : s < L.length := hst.trans htlen
  have hsposL : 0 < L[s] := by
    simpa only [List.getElem_take] using hsposTake
  have hsgetpos : 0 < L.getD s 0 := by
    rw [List.getD_eq_getElem L 0 hslen]
    exact hsposL
  have hsocc : Occupied p N s := by
    dsimp [Occupied]
    dsimp [L] at hsgetpos
    rw [Nat.getD_digits N s hp2] at hsgetpos
    exact hsgetpos
  have ht1 : 1 ≤ t := by omega
  have hsame : Even s ↔ Even t := by
    rcases huniform with hevenUniform | hoddUniform
    · rcases hevenUniform with ⟨heven, hodd⟩
      have htEven : Even t := by
        by_contra htNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_neg htNotEven, hodd] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hsEven : Even s := by
        by_contra hsNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := s) hp2
        rw [if_neg hsNotEven, hodd] at hbound
        have hspos : 0 < digitAt p N s := hsocc
        omega
      exact ⟨fun _ ↦ htEven, fun _ ↦ hsEven⟩
    · rcases hoddUniform with ⟨heven, hodd⟩
      have htNotEven : ¬ Even t := by
        intro htEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_pos htEven, heven] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hsNotEven : ¬ Even s := by
        intro hsEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := s) hp2
        rw [if_pos hsEven, heven] at hbound
        have hspos : 0 < digitAt p N s := hsocc
        omega
      constructor
      · intro hsEven
        exact (hsNotEven hsEven).elim
      · intro htEven
        exact (htNotEven htEven).elim
  have hs_succ_lt : s + 1 < t := by
    have hsle : s + 1 ≤ t := by omega
    by_contra hnot
    have heq : s + 1 = t := by omega
    have hflip : Even t ↔ ¬ Even s := by
      rw [← heq]
      exact Nat.even_add_one
    by_cases hsEven : Even s
    · exact (hflip.mp (hsame.mp hsEven)) hsEven
    · exact hsEven (hsame.mpr (hflip.mpr hsEven))
  have hsltpred : s < t - 1 := by omega
  have hpredzero : digitAt p N (t - 1) = 0 := by
    rcases huniform with hevenUniform | hoddUniform
    · rcases hevenUniform with ⟨heven, hodd⟩
      have htEven : Even t := by
        by_contra htNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_neg htNotEven, hodd] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hpredNotEven : ¬ Even (t - 1) := by
        have h := htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one] at h
        exact h
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_neg hpredNotEven, hodd] at hbound
      omega
    · rcases hoddUniform with ⟨heven, hodd⟩
      have htNotEven : ¬ Even t := by
        intro htEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_pos htEven, heven] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hpredEven : Even (t - 1) := by
        by_contra hpredNotEven
        apply htNotEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one]
        exact hpredNotEven
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_pos hpredEven, heven] at hbound
      omega
  have hNmod : N % p ^ t = N % p ^ (t - 1) := by
    have h := mod_pow_succ_eq_mod_add_digitAt p N (t - 1)
    rw [Nat.sub_add_cancel ht1] at h
    simpa [hpredzero] using h
  have hNmodlt : N % p ^ t < p ^ (t - 1) := by
    rw [hNmod]
    exact Nat.mod_lt _ (pow_pos hp0 _)
  have hpow_s_lt_pred : p ^ s < p ^ (t - 1) := by
    exact Nat.pow_lt_pow_right hp1 hsltpred
  let k := p ^ (t - 1) + p ^ s
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hkltpow : k < p ^ t := by
    have hlt2 : p ^ (t - 1) + p ^ s < 2 * p ^ (t - 1) := by
      omega
    have h2p : 2 * p ^ (t - 1) ≤ p * p ^ (t - 1) := by
      exact Nat.mul_le_mul_right _ hp2
    dsimp [k]
    calc
      p ^ (t - 1) + p ^ s < 2 * p ^ (t - 1) := hlt2
      _ ≤ p * p ^ (t - 1) := h2p
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel ht1]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp [k]
    rw [Nat.add_mod,
      pow_mod_eq_parity_sign hm2 hpmod,
      pow_mod_eq_parity_sign hm2 hpmod]
    by_cases htEven : Even t
    · have hsEven : Even s := hsame.mpr htEven
      have hpredNotEven : ¬ Even (t - 1) := by
        have h := htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one] at h
        exact h
      simp [hpredNotEven, hsEven, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    · have hsNotEven : ¬ Even s := by
        intro hsEven
        exact htEven (hsame.mp hsEven)
      have hpredEven : Even (t - 1) := by
        by_contra hpredNotEven
        apply htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one]
        exact hpredNotEven
      rw [if_pos hpredEven, if_neg hsNotEven]
      rw [Nat.add_comm, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
  have hsmodbase : p ^ s ≤ N % p ^ (s + 1) := by
    rw [mod_pow_succ_eq_mod_add_digitAt]
    have hspos : 0 < digitAt p N s := hsocc
    have hdigit : 1 ≤ digitAt p N s := by omega
    have hmul : p ^ s ≤ p ^ s * digitAt p N s := by
      calc
        p ^ s = p ^ s * 1 := by simp
        _ ≤ p ^ s * digitAt p N s := Nat.mul_le_mul_left _ hdigit
    exact hmul.trans (Nat.le_add_left _ _)
  have hsmodle {j : ℕ} (hsj : s < j) : p ^ s ≤ N % p ^ j := by
    have hs1j : s + 1 ≤ j := by omega
    have hdvd : p ^ (s + 1) ∣ p ^ j := Nat.pow_dvd_pow p hs1j
    have hrem :
        N % p ^ (s + 1) ≤ N % p ^ j := by
      calc
        N % p ^ (s + 1) = (N % p ^ j) % p ^ (s + 1) :=
          (Nat.mod_mod_of_dvd N hdvd).symm
        _ ≤ N % p ^ j := Nat.mod_le _ _
    exact hsmodbase.trans hrem
  have hnocarry_of_lt {j : ℕ} (hjt : j < t) : ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    by_cases hjs : j ≤ s
    · have hjpred : j ≤ t - 1 := by omega
      have hdvdk : p ^ j ∣ k := by
        dsimp [k]
        exact dvd_add
          (Nat.pow_dvd_pow p hjpred)
          (Nat.pow_dvd_pow p hjs)
      rw [Nat.mod_eq_zero_of_dvd hdvdk]
      exact Nat.zero_le _
    · have hsj : s < j := by omega
      have hjpred : j ≤ t - 1 := by omega
      have hdvdtop : p ^ j ∣ p ^ (t - 1) :=
        Nat.pow_dvd_pow p hjpred
      have hpslt : p ^ s < p ^ j :=
        Nat.pow_lt_pow_right hp1 hsj
      have hkmod : k % p ^ j = p ^ s := by
        dsimp [k]
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvdtop]
        simp [Nat.mod_eq_of_lt hpslt]
      rw [hkmod]
      exact hsmodle hsj
  have hpowpred_le_k : p ^ (t - 1) ≤ k := by
    dsimp [k]
    exact Nat.le_add_right _ _
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
  exact ⟨t, s, k, hst, htocc, hsocc, rfl, ⟨hkpos, hkN, hmk⟩, hval⟩
end PascalMinusOne
