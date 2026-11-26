-- Prove2me | solution 1 for PascalMinusOne.plus_one_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:15.908033+00:00
-- url     : https://prove2.me/submissions/c6120f04-9ab0-4fcc-9326-dac977b21b2f

import Definitions.Def_PascalMinusOne_MinusOne
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_PlusOne
import Theorems.Thm_P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45
import Theorems.Thm_P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5
import Theorems.Thm_P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091
import Theorems.Thm_P2M_PascalMinusOne_ofDigits_le_of_forall__1f91a730a18e
import Theorems.Thm_P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_padicVal_G_eq_of_lower_bound_of_witness
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


section
namespace PascalMinusOne
private lemma dvd_iff_digitSum {m p n : ℕ}
    (hpm : p % m = 1 % m) :
    m ∣ n ↔ m ∣ (Nat.digits p n).sum := by
  have hpmod : p ≡ 1 [MOD m] := hpm
  have hmod : n ≡ (Nat.digits p n).sum [MOD m] := by
    calc
      n = Nat.ofDigits p (Nat.digits p n) := (Nat.ofDigits_digits p n).symm
      _ ≡ Nat.ofDigits 1 (Nat.digits p n) [MOD m] :=
        Nat.ofDigits_modEq' p 1 m hpmod (Nat.digits p n)
      _ = (Nat.digits p n).sum := Nat.ofDigits_one _
  exact hmod.dvd_iff (dvd_refl m)
private lemma exists_subdigits_with_sum
    (D : List ℕ) {r : ℕ} (hr : r ≤ D.sum) :
    ∃ S : List ℕ, List.Forall₂ (· ≤ ·) S D ∧ S.sum = r := by
  induction D generalizing r with
  | nil =>
      simp at hr
      subst r
      exact ⟨[], List.Forall₂.nil, rfl⟩
  | cons d D ih =>
      by_cases hrd : r ≤ d
      · obtain ⟨T, hTD, hTsum⟩ :=
          ih (r := 0) (Nat.zero_le _)
        refine ⟨r :: T, List.Forall₂.cons hrd hTD, ?_⟩
        simp [hTsum]
      · have hdr : d < r := Nat.lt_of_not_ge hrd
        have hrem : r - d ≤ D.sum := by
          simp only [List.sum_cons] at hr
          omega
        obtain ⟨T, hTD, hTsum⟩ := ih hrem
        refine ⟨d :: T, List.Forall₂.cons (Nat.le_refl d) hTD, ?_⟩
        simp [hTsum]
        omega
private lemma ofDigits_pos_of_sum_pos
    {p : ℕ} (hp : 0 < p) {L : List ℕ} (hL : 0 < L.sum) :
    0 < Nat.ofDigits p L := by
  induction L with
  | nil => simp at hL
  | cons d D ih =>
      simp only [List.sum_cons] at hL
      simp only [Nat.ofDigits]
      by_cases hd : 0 < d
      · exact Nat.add_pos_left hd _
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        subst d
        have hL' : 0 < D.sum := by simpa using hL
        simpa using Nat.mul_pos hp (ih hL')
private lemma digitSum_pos_of_pos
    {p n : ℕ} (hn : 0 < n) :
    0 < (Nat.digits p n).sum := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hdigits : Nat.digits p n ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr hn0
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨(Nat.digits p n).getLast hdigits, List.getLast_mem hdigits,
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn0)⟩
private lemma exists_append_two_of_two_le_length
    {α : Type*} (L : List α) (hL : 2 ≤ L.length) :
    ∃ P a d, L = P ++ [a, d] := by
  let R := L.reverse
  have hR : 2 ≤ R.length := by
    simpa [R] using hL
  cases hEq : R with
  | nil =>
      simp [hEq] at hR
  | cons d T =>
      cases hTEq : T with
      | nil =>
          simp [hEq, hTEq] at hR
      | cons a P =>
          refine ⟨P.reverse, a, d, ?_⟩
          dsimp [R] at hEq
          have hrev := congrArg List.reverse hEq
          simpa [hTEq, List.append_assoc] using hrev
private theorem plus_one_zero_witness
    {m p N : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : p % m = 1 % m) (hsum : m < (Nat.digits p N).sum) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let D := Nat.digits p N
  obtain ⟨S, hSD, hSsum⟩ :=
    exists_subdigits_with_sum D (Nat.le_of_lt hsum)
  have hD : ∀ d ∈ D, d < p := by
    intro d hd
    exact Nat.digits_lt_base hp.one_lt hd
  have hS : ∀ s ∈ S, s < p :=
    all_lt_of_forall₂_le hSD hD
  let k := Nat.ofDigits p S
  have hkLe : k ≤ N := by
    dsimp [k, D] at *
    calc
      Nat.ofDigits p S ≤ Nat.ofDigits p (Nat.digits p N) :=
        ofDigits_le_of_forall₂ p hSD
      _ = N := Nat.ofDigits_digits p N
  have hSne : S ≠ D := by
    intro hEq
    have hsumEq := congrArg List.sum hEq
    rw [hSsum] at hsumEq
    dsimp [D] at hsumEq
    omega
  have hkNe : k ≠ N := by
    intro hkEq
    apply hSne
    apply Nat.ofDigits_inj_of_len_eq hp.one_lt hSD.length_eq hS hD
    dsimp [k, D] at hkEq ⊢
    calc
      Nat.ofDigits p S = N := hkEq
      _ = Nat.ofDigits p (Nat.digits p N) := (Nat.ofDigits_digits p N).symm
  have hkN : k < N := lt_of_le_of_ne hkLe hkNe
  have hkpos : 0 < k := by
    dsimp [k]
    apply ofDigits_pos_of_sum_pos hp.pos
    rw [hSsum]
    exact hm
  have hKdigitSum :
      (Nat.digits p k).sum = S.sum := by
    dsimp [k]
    exact Nat.sum_digits_ofDigits_eq_sum hp.one_lt
      (l := S.length) (L := S) ⟨rfl, hS⟩
  have hmk : m ∣ k := by
    apply (dvd_iff_digitSum hpm).2
    rw [hKdigitSum, hSsum]
  have hdigit : DigitwiseLE p k N := by
    dsimp [k, D] at *
    simpa only [Nat.ofDigits_digits] using
      (digitwiseLE_of_forall₂_ofDigits hp.two_le hSD hS hD)
  have hval0 :
      padicValNat p (N.choose k) = 0 :=
    (padicVal_choose_eq_zero_iff_digitwiseLE (p := p) (n := N) (k := k) hkN.le).2
      hdigit
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval0⟩
private theorem plus_one_one_witness
    {m p N : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : p % m = 1 % m) (hNm : m < N)
    (hsum : (Nat.digits p N).sum = m) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmp : m < p := by
    by_cases hm1 : m = 1
    · rw [hm1]
      exact hp.one_lt
    · have hmgt1 : 1 < m := by omega
      by_contra hnot
      have hple : p ≤ m := Nat.le_of_not_gt hnot
      by_cases hpeq : p = m
      · subst p
        rw [Nat.mod_self, Nat.mod_eq_of_lt hmgt1] at hpm
        omega
      · have hplt : p < m := lt_of_le_of_ne hple hpeq
        rw [Nat.mod_eq_of_lt hplt, Nat.mod_eq_of_lt hmgt1] at hpm
        have hp2 := hp.two_le
        omega
  have hNpos : 0 < N := lt_trans hm hNm
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  have hlen : 2 ≤ (Nat.digits p N).length := by
    by_contra hnot
    have hle : (Nat.digits p N).length ≤ 1 := by omega
    cases hD : Nat.digits p N with
    | nil =>
        have hN0 : N = 0 :=
          Nat.digits_eq_nil_iff_eq_zero.mp hD
        exact hNne hN0
    | cons d T =>
        cases hT : T with
        | nil =>
            have hNval := Nat.ofDigits_digits p N
            rw [hD, hT] at hNval
            simp only [Nat.ofDigits, mul_zero, add_zero] at hNval
            have hsum' := hsum
            rw [hD, hT] at hsum'
            simp only [List.sum_cons, List.sum_nil, add_zero] at hsum'
            have hEq : N = m := hNval.symm.trans hsum'
            exact (Nat.ne_of_gt hNm) hEq
        | cons a P =>
            simp [hD, hT] at hle
  obtain ⟨P, a, d, hDdecomp⟩ :=
    exists_append_two_of_two_le_length (Nat.digits p N) hlen
  have hDne : Nat.digits p N ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr hNne
  have hdne : d ≠ 0 := by
    have hlast := Nat.getLast_digit_ne_zero p hNne
    have hlastEq :
        (Nat.digits p N).getLast hDne = d := by
      simp [hDdecomp, List.append_assoc]
    rw [hlastEq] at hlast
    exact hlast
  have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
  have hDbound : ∀ x ∈ Nat.digits p N, x < p := by
    intro x hx
    exact Nat.digits_lt_base hp.one_lt hx
  have hPbound : ∀ x ∈ P, x < p := by
    intro x hx
    apply hDbound x
    rw [hDdecomp]
    exact List.mem_append_left _ hx
  have ha_lt : a < p := by
    apply hDbound a
    rw [hDdecomp]
    simp
  have hd_lt : d < p := by
    apply hDbound d
    rw [hDdecomp]
    simp
  have hsumDecomp : P.sum + a + d = m := by
    have hsum' := hsum
    rw [hDdecomp, List.sum_append] at hsum'
    simpa [Nat.add_assoc] using hsum'
  have ha1_lt : a + 1 < p := by
    omega
  let K : List ℕ := P ++ [a + 1, d - 1]
  let R : List ℕ := List.replicate P.length 0 ++ [p - 1]
  have hKbound : ∀ x ∈ K, x < p := by
    intro x hx
    dsimp [K] at hx
    rcases List.mem_append.mp hx with hxP | hxTail
    · exact hPbound x hxP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxTail
      rcases hxTail with rfl | rfl
      · exact ha1_lt
      · omega
  have hRbound : ∀ x ∈ R, x < p := by
    intro x hx
    dsimp [R] at hx
    rcases List.mem_append.mp hx with hxZero | hxLast
    · have hx0 : x = 0 := by
        simpa using (List.eq_of_mem_replicate hxZero)
      subst x
      exact hp.pos
    · have hxpm1 : x = p - 1 := by simpa using hxLast
      subst x
      omega
  have hKsum : K.sum = m := by
    dsimp [K]
    rw [List.sum_append]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    omega
  have hRsum : R.sum = p - 1 := by
    dsimp [R]
    simp
  have hlocal :
      (Nat.ofDigits (p : ℕ) [a + 1, d - 1] : ℕ) +
          Nat.ofDigits (p : ℕ) [p - 1] =
        Nat.ofDigits (p : ℕ) [a, d] := by
    simp only [Nat.ofDigits, Nat.cast_id, mul_zero, add_zero]
    have hpback : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    calc
      (a + 1 + p * (d - 1)) + (p - 1) =
          a + p * (d - 1) + ((p - 1) + 1) := by
            ac_rfl
      _ = a + p * (d - 1) + p := by rw [hpback]
      _ = a + p * ((d - 1) + 1) := by
            simp [Nat.mul_add, Nat.add_assoc]
      _ = a + p * d := by rw [Nat.sub_add_cancel hdpos]
  have hKR :
      Nat.ofDigits p K + Nat.ofDigits p R = N := by
    calc
      Nat.ofDigits p K + Nat.ofDigits p R =
          Nat.ofDigits p P +
            p ^ P.length *
              (Nat.ofDigits p [a + 1, d - 1] + Nat.ofDigits p [p - 1]) := by
            dsimp [K, R]
            simp [Nat.ofDigits_append, Nat.mul_add, Nat.add_assoc]
      _ = Nat.ofDigits p P + p ^ P.length * Nat.ofDigits p [a, d] := by
            rw [hlocal]
      _ = Nat.ofDigits p (P ++ [a, d]) := by
            rw [Nat.ofDigits_append]
      _ = N := by
            rw [← hDdecomp, Nat.ofDigits_digits]
  let k := Nat.ofDigits p K
  let r := Nat.ofDigits p R
  have hKdigitSum : (Nat.digits p k).sum = m := by
    dsimp [k]
    rw [Nat.sum_digits_ofDigits_eq_sum hp.one_lt
      (l := K.length) (L := K) ⟨rfl, hKbound⟩, hKsum]
  have hRdigitSum : (Nat.digits p r).sum = p - 1 := by
    dsimp [r]
    rw [Nat.sum_digits_ofDigits_eq_sum hp.one_lt
      (l := R.length) (L := R) ⟨rfl, hRbound⟩, hRsum]
  have hkpos : 0 < k := by
    dsimp [k]
    apply ofDigits_pos_of_sum_pos hp.pos
    rw [hKsum]
    exact hm
  have hrpos : 0 < r := by
    dsimp [r]
    apply ofDigits_pos_of_sum_pos hp.pos
    rw [hRsum]
    omega
  have hkplusr : k + r = N := by
    dsimp [k, r]
    exact hKR
  have hkN : k < N := by omega
  have hmk : m ∣ k := by
    apply (dvd_iff_digitSum hpm).2
    rw [hKdigitSum]
  have hval : padicValNat p (N.choose k) = 1 := by
    have hs :=
      sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
        (p := p) (k := k) (n := r)
    have hrk : r + k = N := by omega
    rw [hrk, hKdigitSum, hRdigitSum, hsum] at hs
    have hs' :
        (p - 1) * padicValNat p (N.choose k) = p - 1 := by
      simpa using hs
    apply Nat.mul_left_cancel (Nat.sub_pos_of_lt hp.one_lt)
    simpa using hs'
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval⟩
end PascalMinusOne
end

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {m p N : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : p % m = 1 % m) (hmN : m ∣ N) (hNm : m < N) :
    padicValNat p (G N m) = plusOneExpectedValuation m p N := by
  have hNpos : 0 < N := lt_trans hm hNm
  have hsumpos : 0 < (Nat.digits p N).sum :=
    digitSum_pos_of_pos hNpos
  have hsumdiv : m ∣ (Nat.digits p N).sum :=
    (dvd_iff_digitSum hpm).1 hmN
  have hmleSum : m ≤ (Nat.digits p N).sum :=
    Nat.le_of_dvd hsumpos hsumdiv
  by_cases hminimal : (Nat.digits p N).sum = m
  · have hpositive :
        ∀ k, Admissible N m k → 1 ≤ padicValNat p (N.choose k) := by
      intro k hkadm
      rcases hkadm with ⟨hkpos, hkN, hmk⟩
      by_contra hnot
      have hval0 : padicValNat p (N.choose k) = 0 := by omega
      letI : Fact p.Prime := ⟨hp⟩
      have hdigit : DigitwiseLE p k N :=
        (padicVal_choose_eq_zero_iff_digitwiseLE (p := p) (n := N) (k := k)
          hkN.le).1 hval0
      let S := Nat.digitsAppend p (Nat.digits p N).length k
      have hSD :
          List.Forall₂ (· ≤ ·) S (Nat.digits p N) := by
        dsimp [S]
        exact digitsAppend_forall₂_of_digitwiseLE hp.two_le hkN.le hdigit
      have hSval : Nat.ofDigits p S = k := by
        dsimp [S]
        rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
          Nat.ofDigits_digits]
      have hSne : S ≠ Nat.digits p N := by
        intro hEq
        have hkEqN : k = N := by
          calc
            k = Nat.ofDigits p S := hSval.symm
            _ = Nat.ofDigits p (Nat.digits p N) :=
              congrArg (Nat.ofDigits p) hEq
            _ = N := Nat.ofDigits_digits p N
        exact (Nat.ne_of_lt hkN) hkEqN
      have hsumlt :=
        sum_lt_of_forall₂_of_ne hSD hSne
      have hSsum :
          S.sum = (Nat.digits p k).sum := by
        dsimp [S]
        simp [Nat.digitsAppend]
      have hksumlt : (Nat.digits p k).sum < m := by
        calc
          (Nat.digits p k).sum = S.sum := hSsum.symm
          _ < (Nat.digits p N).sum := hsumlt
          _ = m := hminimal
      have hksumpos : 0 < (Nat.digits p k).sum :=
        digitSum_pos_of_pos hkpos
      have hksumdiv : m ∣ (Nat.digits p k).sum :=
        (dvd_iff_digitSum hpm).1 hmk
      have hmle : m ≤ (Nat.digits p k).sum :=
        Nat.le_of_dvd hksumpos hksumdiv
      omega
    obtain ⟨k, hkadm, hkval⟩ :=
      plus_one_one_witness hm hp hpm hNm hminimal
    have hG1 :
        padicValNat p (G N m) = 1 :=
      padicVal_G_eq_of_lower_bound_of_witness
        hm hNm hp hpositive ⟨k, hkadm, hkval⟩
    simpa [plusOneExpectedValuation, hminimal] using hG1
  · have hsumgt : m < (Nat.digits p N).sum := by
      exact lt_of_le_of_ne hmleSum (Ne.symm hminimal)
    obtain ⟨k, hkadm, hkval⟩ :=
      plus_one_zero_witness hm hp hpm hsumgt
    have hG0 :
        padicValNat p (G N m) = 0 :=
      padicVal_G_eq_of_lower_bound_of_witness
        hm hNm hp (fun _ _ ↦ Nat.zero_le _) ⟨k, hkadm, hkval⟩
    simpa [plusOneExpectedValuation, hminimal] using hG0
end PascalMinusOne
