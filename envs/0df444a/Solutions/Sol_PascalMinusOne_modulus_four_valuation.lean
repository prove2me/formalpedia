-- Prove2me | solution 1 for PascalMinusOne.modulus_four_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:26:44.798739+00:00
-- url     : https://prove2.me/submissions/85b15430-fd1d-40b9-93ac-e4cb87ae8da8

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
private lemma prime_mod_four_eq_one_or_three
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hlt : p % 4 < 4 := Nat.mod_lt _ (by omega)
  by_cases h1 : p % 4 = 1
  · exact Or.inl h1
  by_cases h3 : p % 4 = 3
  · exact Or.inr h3
  have hrem : p % 4 = 0 ∨ p % 4 = 2 := by omega
  have h2dvd : 2 ∣ p := by
    rcases hrem with h0 | h2
    · have hdecomp := Nat.mod_add_div p 4
      refine ⟨2 * (p / 4), ?_⟩
      omega
    · have hdecomp := Nat.mod_add_div p 4
      refine ⟨2 * (p / 4) + 1, ?_⟩
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
    {p N : ℕ} (hp : p.Prime) (h4N : 4 ∣ N) (hN : 4 < N) :
    padicValNat p (G N 4) = modulusFourExpectedValuation p N := by
  by_cases hp2 : p = 2
  · subst p
    rcases h4N with ⟨n, rfl⟩
    have hn : 1 < n := by omega
    have hscale :=
      scaling_valuation (p := 2) (c := 2) (q := 1) (N' := n) hp
    have hplus :=
      plus_one_valuation (m := 1) (p := 2) (N := n)
        (by omega) hp (by simp) (Nat.one_dvd n) hn
    rw [modulusFourExpectedValuation, if_pos rfl]
    have hs :
        padicValNat 2 (G (4 * n) 4) =
          padicValNat 2 (G n 1) := by
      simpa using hscale
    have hdiv : (4 * n) / 4 = n := by
      simpa [Nat.mul_comm] using (Nat.mul_div_left n (by omega : 0 < 4))
    rw [hdiv]
    exact hs.trans hplus
  · rcases prime_mod_four_eq_one_or_three hp hp2 with h1 | h3
    · rw [modulusFourExpectedValuation, if_neg hp2, if_pos h1]
      exact
        plus_one_valuation (m := 4) (p := p) (N := N)
          (by omega) hp (by simpa using h1) h4N hN
    · have hnot1 : p % 4 ≠ 1 := by omega
      rw [modulusFourExpectedValuation, if_neg hp2, if_neg hnot1]
      exact
        minus_one_valuation (m := 4) (N := N) (p := p)
          (by omega) h4N hN hp (by simpa using h3)
end PascalMinusOne
