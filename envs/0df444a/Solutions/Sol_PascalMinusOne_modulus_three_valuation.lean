-- Prove2me | solution 1 for PascalMinusOne.modulus_three_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:26:44.146996+00:00
-- url     : https://prove2.me/submissions/dbf7c76f-c46f-4a1d-a1bf-a4ae2b2fa49e

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
private lemma prime_mod_three_eq_one_or_two
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hlt : p % 3 < 3 := Nat.mod_lt _ (by omega)
  by_cases h1 : p % 3 = 1
  · exact Or.inl h1
  by_cases h2 : p % 3 = 2
  · exact Or.inr h2
  have h0 : p % 3 = 0 := by omega
  have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
  have hEq : 3 = p :=
    (Nat.dvd_prime_two_le hp (by omega)).1 hd
  exact (hp3 hEq.symm).elim
end PascalMinusOne
end

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {p N : ℕ} (hp : p.Prime) (h3N : 3 ∣ N) (hN : 3 < N) :
    padicValNat p (G N 3) = modulusThreeExpectedValuation p N := by
  by_cases hp3 : p = 3
  · subst p
    rcases h3N with ⟨n, rfl⟩
    have hn : 1 < n := by omega
    have hscale :=
      scaling_valuation (p := 3) (c := 1) (q := 1) (N' := n) hp
    have hplus :=
      plus_one_valuation (m := 1) (p := 3) (N := n)
        (by omega) hp (by simp) (Nat.one_dvd n) hn
    rw [modulusThreeExpectedValuation, if_pos rfl]
    have hs :
        padicValNat 3 (G (3 * n) 3) =
          padicValNat 3 (G n 1) := by
      simpa using hscale
    have hdiv : (3 * n) / 3 = n := by
      simpa [Nat.mul_comm] using (Nat.mul_div_left n (by omega : 0 < 3))
    rw [hdiv]
    exact hs.trans hplus
  · rcases prime_mod_three_eq_one_or_two hp hp3 with h1 | h2
    · rw [modulusThreeExpectedValuation, if_neg hp3, if_pos h1]
      exact
        plus_one_valuation (m := 3) (p := p) (N := N)
          (by omega) hp (by simpa using h1) h3N hN
    · have hnot1 : p % 3 ≠ 1 := by omega
      rw [modulusThreeExpectedValuation, if_neg hp3, if_neg hnot1]
      exact
        minus_one_valuation (m := 3) (N := N) (p := p)
          (by omega) h3N hN hp (by simpa using h2)
end PascalMinusOne
