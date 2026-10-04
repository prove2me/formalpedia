-- Prove2me | solution 1 for OddPerfectNumber.Kernel.cyclotomic_plus_prime_is_quadratic_residue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:01:20.478978+00:00
-- url     : https://prove2.me/submissions/6f5c143b-d8fd-4eb8-b94d-af552b36cd49

import Mathlib

theorem solution {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqd : q ∣ p ^ 2 + p + 1) :
    q % 6 = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hq3' : q ≠ 3 := by simpa using hq3
  -- q is odd: p^2+p+1 is odd
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ p * (p + 1) := (Nat.even_mul_succ_self p).two_dvd
    have : p ^ 2 + p + 1 = p * (p + 1) + 1 := by ring
    rw [this] at hqd
    omega
  set x : ZMod q := (p : ZMod q) with hx
  have h0 : x ^ 2 + x + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ q).2 hqd
    simpa [hx] using this
  have h3 : x ^ 3 = 1 := by
    have : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
    rw [h0, mul_zero, sub_eq_zero] at this
    exact this
  have h1 : x ≠ 1 := by
    intro h
    rw [h] at h0
    norm_num at h0
    have h3z : ((3 : ℕ) : ZMod q) = 0 := by
      rw [← h0]; push_cast; ring
    rw [ZMod.natCast_eq_zero_iff] at h3z
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3z
    exact hq3' this
  have hne : x ≠ 0 := by
    intro h
    rw [h] at h0
    norm_num at h0
  have hord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 h1
  have hdvd := ZMod.orderOf_dvd_card_sub_one hne
  rw [hord] at hdvd
  have hodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  have hq1 : 2 ≤ q := hq.two_le
  omega
