-- Prove2me | solution 1 for OddPerfectNumber.k_one_p_valuation_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:44:08.546371+00:00
-- url     : https://prove2.me/submissions/318a7d87-cce1-4f34-b96c-ccd7e2747afa

import Mathlib

theorem solution (p m e : Nat)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hd : m ^ 2 = ((p + 1) / 2) * e)
    (hsig : (∑ d ∈ (m ^ 2).divisors, d) = p * e) :
    padicValNat p (∑ d ∈ (m ^ 2).divisors, d) = 1 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  -- `p ∤ m^2` since `p` is prime and `p ∤ m`.
  have hpm2 : ¬ p ∣ m ^ 2 := by
    intro h
    rw [pow_two] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hpm h1
    · exact hpm h1
  -- Hence `p ∤ e`, as `e ∣ m^2`.
  have he : e ∣ m ^ 2 := ⟨(p + 1) / 2, hd.trans (mul_comm _ _)⟩
  have hpde : ¬ p ∣ e := fun h => hpm2 (dvd_trans h he)
  have he0 : e ≠ 0 := by
    intro h
    rw [h, mul_zero] at hd
    exact pow_ne_zero 2 hm0 hd
  -- `v_p(σ) = v_p(p * e) = v_p(p) + v_p(e) = 1 + 0`.
  rw [hsig, padicValNat.mul hp.ne_zero he0, padicValNat.self hp.one_lt,
    padicValNat.eq_zero_of_not_dvd hpde]
