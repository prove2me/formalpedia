-- Prove2me | solution 1 for OddPerfectNumber.Kernel.cyclotomic_plus_prime_order_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T19:59:57.466646+00:00
-- url     : https://prove2.me/submissions/be46b99a-35c5-4638-baed-3f70664370d7

import Mathlib

set_option autoImplicit false

lemma cycPlusc3b0_aux {p q : ℕ} [Fact q.Prime] (hq : q.Prime) (hq3 : q ≠ 3)
    (hqd : q ∣ p ^ 2 + p + 1) : orderOf (p : ZMod q) = 3 := by
  have hcast : ((p : ZMod q)) ^ 2 + (p : ZMod q) + 1 = 0 := by
    have h1 : ((p ^ 2 + p + 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hqd
    push_cast at h1
    exact h1
  set x : ZMod q := (p : ZMod q) with hx
  have h3 : x ^ 3 = 1 := by linear_combination (x - 1) * hcast
  have hx1 : x ≠ 1 := by
    intro h1
    have h30 : ((3 : ℕ) : ZMod q) = 0 := by
      rw [h1] at hcast
      push_cast
      linear_combination hcast
    have := (ZMod.natCast_eq_zero_iff 3 q).mp h30
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp this)
  exact orderOf_eq_prime h3 hx1

theorem solution {p q : Nat} [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hq : q.Prime) (hq3 : q != 3)
    (hqd : q ∣ p ^ 2 + p + 1) :
    orderOf (p : ZMod q) = 3 := by
  have hq3' : q ≠ 3 := by simpa using hq3
  exact cycPlusc3b0_aux hq hq3' hqd
