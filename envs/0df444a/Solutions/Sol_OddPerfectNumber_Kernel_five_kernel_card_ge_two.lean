-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_kernel_card_ge_two
-- status  : ACCEPTED   (disprove)
-- author  : @os0xcom
-- created : 2026-10-03T15:59:16.855533+00:00
-- url     : https://prove2.me/submissions/df80a61f-2b74-4831-adca-76dd22663535

import Mathlib

set_option linter.unusedVariables false

theorem solution :
    ¬ (∀ (p m s d1 d2 : Nat) (_hp : p.Prime) (_hp2 : p != 2) (_hp4 : p % 4 = 1)
        (_hm : Odd m) (_hpm : ¬ p ∣ m) (_hs : ¬ ∃ r : Nat, s = r ^ 2)
        (_hd : d1 ^ 2 * d2 = s) (_hd2 : 0 < d2) (_hsf : Squarefree d2),
        2 ≤ d2.primeFactors.card) := by
  intro H
  have hnsq : ¬ ∃ r : Nat, (3 : Nat) = r ^ 2 := by
    rintro ⟨r, hr⟩
    rcases Nat.lt_trichotomy r 2 with hlt | heq | hgt
    · interval_cases r <;> simp at hr
    · simp [heq] at hr
    · have hmul := Nat.mul_le_mul hgt hgt
      have : r * r = 3 := by simpa [Nat.pow_two] using hr.symm
      omega
  have hsf : Squarefree 3 := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx hdiv
    have hx3 : x ∣ 3 := (dvd_mul_left x x).trans hdiv
    have hxeq : x = 3 := (Nat.prime_dvd_prime_iff_eq hx (by decide)).1 hx3
    rw [hxeq] at hdiv
    exact absurd hdiv (by decide : ¬ 3 * 3 ∣ 3)
  have h :=
    H 5 1 3 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) hnsq
      (by decide) (by decide) hsf
  have hcard : (3 : Nat).primeFactors.card = 1 := by
    rw [(by decide : Nat.Prime 3).primeFactors]
    simp
  have : (2 : Nat) ≤ 1 := by simpa [hcard] using h
  omega
