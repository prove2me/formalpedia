-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_ne_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:02:32.843982+00:00
-- url     : https://prove2.me/submissions/aa751685-075f-4119-9851-d85682807ec0

-- Assembler for b≠1 (half-exponent convention: b is half of full 5-exponent).
-- D=15 handled at p/d level; D∈{27,31,45,75,87} via D-bridge + weak terminals.
-- Requires smooth ACCEPTED before submission.
import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp3_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp3_ne_two_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp29_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp5_eq_one_forces_q4_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D15_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_q4_31_D_le_106_weak_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_smooth_D_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_full_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D27_q4_31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D31_q4_31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D45_q4_31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D75_q4_31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D87_q4_31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D3_q4_31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D9_q4_31_absurd_v1

theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (h29exp : (m ^ 2).factorization 29 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 1 := by
  intro hb1
  have ha1 : a ≠ 1 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp3_ne_one_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he
  have ha2 : a ≠ 2 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp3_ne_two_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he
  have hc1 : c ≠ 1 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp29_ne_one_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he
  have ha3 : 3 ≤ a := by omega
  have hc2 : 2 ≤ c := by omega
  have he1 : 1 ≤ e := by omega
  have hq4eq : q4 = 31 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_eq_one_forces_q4_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he hb1
  -- D-bridge: D = (p+1)/2, p odd from p%4=1
  have hpodd : Odd p := by
    have h2 : p % 2 = 1 := by omega
    exact Nat.odd_iff.mpr h2
  obtain ⟨D, hDdef⟩ : ∃ D, D = (p + 1) / 2 := ⟨_, rfl⟩
  have hp_eq : p = 2 * D - 1 := by omega
  -- D15 at p/d level
  by_cases hD15 : D = 15
  · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D15_absurd_v1 p m d q4 a b c e sigma D
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac h29mem ha hb hc he hp_eq hD15
  · -- D-interface chain
    have h1 : m ^ 2 = D * d := by rw [hDdef]; exact hprod
    have h2 : sigma = p * d := by rw [hglobal]; exact hsig
    have hrel : D * sigma = p * m ^ 2 := by rw [h1, h2]; ring
    have hDlt : D < 107 :=
      OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_q4_31_D_le_106_weak_v1 m a b c e D p q4 sigma
        hfac hsigma hrel hp hp_eq hq4prime hq4eq hb1 ha3 hc2 he1
    have hDpos : 0 < D := by omega
    have hm2 : m ^ 2 = D * d := by rw [hDdef]; exact hprod
    have hDm : D ∣ m ^ 2 := ⟨d, hm2⟩
    have hsup2 : ∀ x ∈ (m ^ 2).primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4 := by
      intro x hx
      have hxp : x ∈ m.primeFactors := by
        have hpp : x.Prime := (Nat.mem_primeFactors.mp hx).1
        have hdv : x ∣ m := (Nat.prime_iff.mp hpp).dvd_of_dvd_pow ((Nat.mem_primeFactors.mp hx).2.1)
        exact (Nat.mem_primeFactors).mpr ⟨hpp, hdv, by
          obtain ⟨kodd, hkodd⟩ := hm; omega⟩
      have h := hsupport x hxp
      simpa [hq4eq] using h
    have hmpos : 0 < m := by obtain ⟨kodd, hkodd⟩ := hm; omega
    have hsm : D ∣ 1820475 :=
      OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_smooth_D_v2 D m q4 hDlt hDpos hmpos hDm hsup2 hq4eq
    obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
    have hDform : D = 2 * k + 1 := by rw [hDdef, hk]; omega
    have hDodd2 : D % 2 = 1 := by omega
    have hpD : Nat.Prime (2 * D - 1) := by rw [← hp_eq]; exact hp
    have hD12 : 12 ≤ D := by
      by_contra hlt
      push_neg at hlt
      have hsmall : D = 3 ∨ D = 9 := by
        by_cases h6 : D < 6
        · interval_cases D <;> revert hsm hpD hDpos <;> decide
        · interval_cases D <;> revert hsm hpD hDpos <;> decide
      rcases hsmall with rfl | rfl
      · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D3_q4_31_absurd_v1
          3 p sigma m a b c e q4 hrel rfl hp_eq hsigma hq4eq hpm h5mem
      · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D9_q4_31_absurd_v1
          9 p sigma m a b c e q4 hfac hrel rfl hp_eq hsigma hq4eq ha3 hb1 hc2 he1
    have hDne106 : D ≠ 106 := by
      intro h106
      have hp211 : p = 211 := by omega
      omega
    have hDhi : D ≤ 105 := by omega
    have hcases := OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_full_v1 D hD12 hDhi hsm hpD
    rcases hcases with h | h | h | h | h | h
    · omega
    · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D27_q4_31_absurd_v1 27 p sigma m a b c e q4
        (h ▸ hrel) rfl (h ▸ hp_eq) hsigma hq4eq he
    · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D31_q4_31_absurd_v1 31 p sigma m a b c e q4
        (h ▸ hrel) rfl (h ▸ hp_eq) hsigma hq4eq
    · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D45_q4_31_absurd_v1 m a b c e 45 p q4 sigma
        hfac hsigma (h ▸ hrel) rfl (h ▸ hp_eq) hq4eq hb1 ha3 hc2 he1
    · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D75_q4_31_absurd_v1 m a b c e 75 p q4 sigma
        hfac hsigma (h ▸ hrel) rfl (h ▸ hp_eq) hq4eq hb1 ha3 hc2 he1
    · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D87_q4_31_absurd_v1 m a b c e 87 p q4 sigma
        hfac hsigma (h ▸ hrel) rfl (h ▸ hp_eq) hq4eq hb1 ha3 hc2 he1
