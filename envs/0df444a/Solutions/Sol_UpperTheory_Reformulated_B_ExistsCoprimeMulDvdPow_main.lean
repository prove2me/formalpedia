-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:58.409616+00:00
-- url     : https://prove2.me/submissions/98646e86-b9a2-495b-8427-b2516afcf30f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KeyLemmaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace CoprimeTimesDvdPowFactorization
private theorem key (g m : ℕ) (hm : 0 < m) :
    (m / Nat.gcd m (g ^ m)).Coprime g := by
  set d := Nat.gcd m (g ^ m) with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hm
  have hcop : (m / d).Coprime (g ^ m / d) := Nat.coprime_div_gcd_div_gcd hdpos
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  have hpn : ¬ p ∣ g ^ m / d := by
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpc hcop) h
  have hdg : d ∣ g ^ m := Nat.gcd_dvd_right _ _
  have hdm : d ∣ m := Nat.gcd_dvd_left _ _
  have hpm : p ^ m ∣ d * (g ^ m / d) := by
    rw [Nat.mul_div_cancel' hdg]
    exact pow_dvd_pow_of_dvd hpg m
  have hcp : Nat.Coprime (p ^ m) (g ^ m / d) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
  have hpd : p ^ m ∣ d := hcp.dvd_of_dvd_mul_right hpm
  have hall : p ^ m * p ∣ d * (m / d) := Nat.mul_dvd_mul hpd hpc
  rw [Nat.mul_div_cancel' hdm, ← pow_succ] at hall
  have hle : p ^ (m + 1) ≤ m := Nat.le_of_dvd hm hall
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
  have h3 : p ^ m ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ m)
  omega
end CoprimeTimesDvdPowFactorization
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow
theorem _root_.solution :
    ∀ (g m : ℕ),
    (0 : ℕ) < m → ∃ (c : ℕ) (d : ℕ), m = c * d ∧ c.Coprime g ∧ d ∣ g ^ m := by
  intro g m hm
  refine ⟨m / Nat.gcd m (g ^ m), Nat.gcd m (g ^ m), ?_, CoprimeTimesDvdPowFactorization.key g m hm, Nat.gcd_dvd_right _ _⟩
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
end UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow
