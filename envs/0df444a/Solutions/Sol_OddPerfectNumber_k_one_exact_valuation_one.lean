-- Prove2me | solution 1 for OddPerfectNumber.k_one_exact_valuation_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:54:04.442555+00:00
-- url     : https://prove2.me/submissions/52632722-41cd-4924-93e7-261bb6f36e22

import Mathlib

theorem solution (p m d : Nat)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) :
    padicValNat p (∑ x ∈ (m ^ 2).divisors, x) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm : m ≠ 0 := by
    intro h
    subst h
    exact hpm (dvd_zero p)
  have hm2 : m ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hm hm
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdvd
    exact hm2 hdvd
  have hpd : ¬ p ∣ d := by
    intro h
    exact hpm (hp.prime.dvd_of_dvd_pow
      (dvd_trans h ⟨_, hdvd.trans (mul_comm _ _)⟩))
  have hval_d : padicValNat p d = 0 := by
    have h1 : ¬ p ^ 1 ∣ d := by simpa using hpd
    have h2 : ¬ 1 ≤ padicValNat p d :=
    fun hle => h1 ((padicValNat_dvd_iff_le hd0).mpr hle)
    omega
  -- NOTE (row 431 CE): `p` must be pinned by an ascribed type *before*
  -- instance synthesis, or `Fact (Nat.Prime ?p)` is stuck on a metavar.
  have hmul : padicValNat p (p * d)
      = padicValNat p p + padicValNat p d :=
    padicValNat.mul hp.pos.ne' hd0
  have hself : padicValNat p p = 1 := padicValNat_self
  -- NOTE (row 433 CE): the goal contains the divisor *sum*, so unfold it
  -- *forward* with `hsig` (`∑` -> `p * d`); `←` finds no `p * d` pattern.
  rw [hsig, hmul, hself, hval_d, add_zero]
