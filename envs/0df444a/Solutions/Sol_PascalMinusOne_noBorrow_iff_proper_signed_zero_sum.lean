-- Prove2me | solution 1 for PascalMinusOne.noBorrow_iff_proper_signed_zero_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:16.599187+00:00
-- url     : https://prove2.me/submissions/82181973-8ccb-46d1-8954-836b805ad673

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_dvd_iff_signedZeroSum_digitSums
import Theorems.Thm_PascalMinusOne_parityDigitSums_add_eq_sum
import Theorems.Thm_PascalMinusOne_parityDigitSums_digitsAppend
import Theorems.Thm_PascalMinusOne_parityDigitSums_mono
import Theorems.Thm_PascalMinusOne_exists_subdigits_with_parityDigitSums
import Theorems.Thm_P2M_PascalMinusOne_ofDigits_le_of_forall__1f91a730a18e
import Theorems.Thm_P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e
import Theorems.Thm_P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45
import Theorems.Thm_P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091
import Theorems.Thm_P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5
import Theorems.Thm_PascalMinusOne_parityDigitSums_digits_ofDigits
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_padicVal_choose_eq_zero_iff_digitwiseLE
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
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1) (hmN : m ∣ N) :
    (∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0) ↔
      HasProperZeroSubmultiset m (evenDigitSum p N) (oddDigitSum p N) := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨k, hkadm, hkval⟩
    rcases hkadm with ⟨hkpos, hkN, hmk⟩
    have hdigit : DigitwiseLE p k N :=
      (padicVal_choose_eq_zero_iff_digitwiseLE (p := p) (n := N) (k := k)
        (Nat.le_of_lt hkN)).1 hkval
    let S := Nat.digitsAppend p (Nat.digits p N).length k
    have hSD : List.Forall₂ (· ≤ ·) S (Nat.digits p N) := by
      dsimp [S]
      exact digitsAppend_forall₂_of_digitwiseLE hp.two_le (Nat.le_of_lt hkN) hdigit
    have hparS :
        parityDigitSums S = parityDigitSums (Nat.digits p k) := by
      dsimp [S]
      exact parityDigitSums_digitsAppend p (Nat.digits p N).length k
    have hmono := parityDigitSums_mono hSD
    unfold HasProperZeroSubmultiset
    refine ⟨evenDigitSum p k, oddDigitSum p k, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hmono.1
      rw [hparS] at h
      simpa [evenDigitSum] using h
    · have h := hmono.2
      rw [hparS] at h
      simpa [oddDigitSum] using h
    · have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
      have hdigits : Nat.digits p k ≠ [] :=
        Nat.digits_ne_nil_iff_ne_zero.mpr hkne
      have hsumpos : 0 < (Nat.digits p k).sum :=
        List.sum_pos_iff_exists_pos_nat.mpr
          ⟨(Nat.digits p k).getLast hdigits, List.getLast_mem hdigits,
            Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hkne)⟩
      simpa [evenDigitSum, oddDigitSum, parityDigitSums_add_eq_sum] using hsumpos
    · have hSval : Nat.ofDigits p S = k := by
        dsimp [S]
        rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
      have hSne : S ≠ Nat.digits p N := by
        intro hEq
        have hkEqN : k = N := by
          calc
            k = Nat.ofDigits p S := hSval.symm
            _ = Nat.ofDigits p (Nat.digits p N) := congrArg (Nat.ofDigits p) hEq
            _ = N := Nat.ofDigits_digits p N
        exact (Nat.ne_of_lt hkN) hkEqN
      have hsumlt := sum_lt_of_forall₂_of_ne hSD hSne
      rw [← parityDigitSums_add_eq_sum S,
        ← parityDigitSums_add_eq_sum (Nat.digits p N)] at hsumlt
      rw [hparS] at hsumlt
      simpa [evenDigitSum, oddDigitSum] using hsumlt
    · exact
        (dvd_iff_signedZeroSum_digitSums (m := m) (p := p) (k := k) (by omega) hpm).1 hmk
  · rintro ⟨a, b, ha, hb, hpos, hproper, hzero⟩
    have haD : a ≤ (parityDigitSums (Nat.digits p N)).1 := by
      simpa [evenDigitSum] using ha
    have hbD : b ≤ (parityDigitSums (Nat.digits p N)).2 := by
      simpa [oddDigitSum] using hb
    obtain ⟨S, hSD, hpar⟩ :=
      exists_subdigits_with_parityDigitSums (Nat.digits p N) haD hbD
    have hD : ∀ d ∈ Nat.digits p N, d < p :=
      fun d hd => Nat.digits_lt_base hp.one_lt hd
    have hS : ∀ s ∈ S, s < p :=
      all_lt_of_forall₂_le hSD hD
    let k := Nat.ofDigits p S
    have hkn : k ≤ N := by
      dsimp [k]
      calc
        Nat.ofDigits p S ≤ Nat.ofDigits p (Nat.digits p N) :=
          ofDigits_le_of_forall₂ p hSD
        _ = N := Nat.ofDigits_digits p N
    have hSne : S ≠ Nat.digits p N := by
      intro hEq
      have htot : evenDigitSum p N + oddDigitSum p N = a + b := by
        have hpair :=
          congrArg (fun q : ℕ × ℕ => q.1 + q.2) hpar
        simpa [hEq, evenDigitSum, oddDigitSum] using hpair
      omega
    have hkneN : k ≠ N := by
      intro hkEq
      apply hSne
      apply Nat.ofDigits_inj_of_len_eq hp.one_lt hSD.length_eq hS hD
      dsimp [k] at hkEq
      calc
        Nat.ofDigits p S = N := hkEq
        _ = Nat.ofDigits p (Nat.digits p N) := (Nat.ofDigits_digits p N).symm
    have hkN : k < N := lt_of_le_of_ne hkn hkneN
    have hsumS : S.sum = a + b := by
      calc
        S.sum = (parityDigitSums S).1 + (parityDigitSums S).2 :=
          (parityDigitSums_add_eq_sum S).symm
        _ = a + b := by rw [hpar]
    have hsumpos : 0 < S.sum := by omega
    have hsumle : S.sum ≤ Nat.ofDigits p S :=
      Nat.sum_le_ofDigits S (Nat.le_of_lt hp.one_lt)
    have hkpos : 0 < k := by
      dsimp [k]
      exact hsumpos.trans_le hsumle
    have hdigit0 :
        DigitwiseLE p (Nat.ofDigits p S) (Nat.ofDigits p (Nat.digits p N)) :=
      digitwiseLE_of_forall₂_ofDigits hp.two_le hSD hS hD
    have hdigit : DigitwiseLE p k N := by
      simpa [k, Nat.ofDigits_digits] using hdigit0
    have hparK :
        parityDigitSums (Nat.digits p k) = (a, b) := by
      dsimp [k]
      exact (parityDigitSums_digits_ofDigits hp.two_le hS).trans hpar
    have heven : evenDigitSum p k = a := by
      simpa [evenDigitSum] using congrArg Prod.fst hparK
    have hodd : oddDigitSum p k = b := by
      simpa [oddDigitSum] using congrArg Prod.snd hparK
    have hzeroK :
        SignedZeroSum m (evenDigitSum p k) (oddDigitSum p k) := by
      rw [heven, hodd]
      exact hzero
    have hmk : m ∣ k :=
      (dvd_iff_signedZeroSum_digitSums (m := m) (p := p) (k := k) (by omega) hpm).2 hzeroK
    have hkval : padicValNat p (N.choose k) = 0 :=
      (padicVal_choose_eq_zero_iff_digitwiseLE (p := p) (n := N) (k := k) hkn).2 hdigit
    exact ⟨k, ⟨hkpos, hkN, hmk⟩, hkval⟩
end PascalMinusOne
