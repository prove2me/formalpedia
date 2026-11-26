-- Prove2me | solution 1 for PascalMinusOne.modulus_six_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:26:45.864018+00:00
-- url     : https://prove2.me/submissions/9e3eac97-85a2-4ecd-b48a-2e0f5593f7b9

import Definitions.Def_PascalMinusOne_PlusOne
import Definitions.Def_PascalMinusOne_Scaling
import Definitions.Def_PascalMinusOne_SmallModuli
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_minus_one_valuation
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_plus_one_valuation
import Theorems.Thm_PascalMinusOne_scaling_valuation
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
private lemma prime_mod_six_eq_one_or_five
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by omega)
  by_cases h1 : p % 6 = 1
  · exact Or.inl h1
  by_cases h5 : p % 6 = 5
  · exact Or.inr h5
  have hrem :
      p % 6 = 0 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 := by
    omega
  rcases hrem with h0 | h2 | h3 | h4
  · have hdecomp := Nat.mod_add_div p 6
    have h2dvd : 2 ∣ p := by
      refine ⟨3 * (p / 6), ?_⟩
      omega
    have hEq : 2 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
    exact (hp2 hEq.symm).elim
  · have hdecomp := Nat.mod_add_div p 6
    have h2dvd : 2 ∣ p := by
      refine ⟨3 * (p / 6) + 1, ?_⟩
      omega
    have hEq : 2 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
    exact (hp2 hEq.symm).elim
  · have hdecomp := Nat.mod_add_div p 6
    have h3dvd : 3 ∣ p := by
      refine ⟨2 * (p / 6) + 1, ?_⟩
      omega
    have hEq : 3 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h3dvd
    exact (hp3 hEq.symm).elim
  · have hdecomp := Nat.mod_add_div p 6
    have h2dvd : 2 ∣ p := by
      refine ⟨3 * (p / 6) + 2, ?_⟩
      omega
    have hEq : 2 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
    exact (hp2 hEq.symm).elim
end PascalMinusOne
end

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {p N : ℕ} (hp : p.Prime) (h6N : 6 ∣ N) (hN : 6 < N) :
    padicValNat p (G N 6) = modulusSixExpectedValuation p N := by
  by_cases hp2 : p = 2
  · subst p
    rcases h6N with ⟨n, rfl⟩
    have hn : 1 < n := by omega
    have hscale :=
      scaling_valuation (p := 2) (c := 1) (q := 3) (N' := 3 * n) hp
    have hminus :=
      minus_one_valuation (m := 3) (N := 3 * n) (p := 2)
        (by omega) (Nat.dvd_mul_right 3 n) (by omega) hp (by decide)
    rw [modulusSixExpectedValuation, if_pos rfl]
    have hs :
        padicValNat 2 (G (6 * n) 6) =
          padicValNat 2 (G (3 * n) 3) := by
      have hNscale : 2 ^ 1 * (3 * n) = 6 * n := by
        simp only [pow_one]
        omega
      have hMscale : 2 ^ 1 * 3 = 6 := by decide
      rw [hNscale, hMscale] at hscale
      exact hscale
    have hdiv : (6 * n) / 2 = 3 * n := by omega
    rw [hdiv]
    exact hs.trans hminus
  · by_cases hp3 : p = 3
    · subst p
      rcases h6N with ⟨n, rfl⟩
      have hn : 1 < n := by omega
      have hscale :=
        scaling_valuation (p := 3) (c := 1) (q := 2) (N' := 2 * n) hp
      have hplus :=
        plus_one_valuation (m := 2) (p := 3) (N := 2 * n)
          (by omega) hp (by decide) (Nat.dvd_mul_right 2 n) (by omega)
      rw [modulusSixExpectedValuation, if_neg hp2, if_pos rfl]
      have hs :
          padicValNat 3 (G (6 * n) 6) =
            padicValNat 3 (G (2 * n) 2) := by
        have hNscale : 3 ^ 1 * (2 * n) = 6 * n := by
          simp only [pow_one]
          omega
        have hMscale : 3 ^ 1 * 2 = 6 := by decide
        rw [hNscale, hMscale] at hscale
        exact hscale
      have hdiv : (6 * n) / 3 = 2 * n := by omega
      rw [hdiv]
      exact hs.trans hplus
    · rcases prime_mod_six_eq_one_or_five hp hp2 hp3 with h1 | h5
      · rw [modulusSixExpectedValuation, if_neg hp2, if_neg hp3, if_pos h1]
        exact
          plus_one_valuation (m := 6) (p := p) (N := N)
            (by omega) hp (by simpa using h1) h6N hN
      · have hnot1 : p % 6 ≠ 1 := by omega
        rw [modulusSixExpectedValuation, if_neg hp2, if_neg hp3, if_neg hnot1]
        exact
          minus_one_valuation (m := 6) (N := N) (p := p)
            (by omega) h6N hN hp (by simpa using h5)
end PascalMinusOne
