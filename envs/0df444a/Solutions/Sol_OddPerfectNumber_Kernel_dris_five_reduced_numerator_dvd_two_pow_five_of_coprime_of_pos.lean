-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_five_reduced_numerator_dvd_two_pow_five_of_coprime_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:01:19.597658+00:00
-- url     : https://prove2.me/submissions/658f9f1f-21d8-491c-aad8-0edcaf771afa

import Mathlib

theorem solution (p m s u v w : Nat)
    (hm0 : m != 0) (hs0 : s != 0)
    (huw : Nat.Coprime u w)
    (hT : (∑ d ∈ (m ^ 2).divisors, d) = u * v)
    (hm2 : m ^ 2 = v * w)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    u ∣ 2 * (p ^ 5 * w) := by
  have hm : m ≠ 0 := by simpa using hm0
  have hpos : 0 < ∑ d ∈ (m ^ 2).divisors, d :=
    Finset.sum_pos (fun i hi => Nat.pos_of_mem_divisors hi)
      (Nat.nonempty_divisors.2 (pow_ne_zero 2 hm))
  have hv : v ≠ 0 := by
    rintro rfl
    rw [hT, Nat.mul_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  have key : ((∑ d ∈ (p ^ 5).divisors, d) * u) * v = (2 * (p ^ 5 * w)) * v := by
    calc ((∑ d ∈ (p ^ 5).divisors, d) * u) * v
        = (∑ d ∈ (p ^ 5).divisors, d) * (u * v) := by ring
      _ = (∑ d ∈ (p ^ 5).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) := by rw [hT]
      _ = p ^ 5 * ((∑ d ∈ (p ^ 5).divisors, d) * s) := by rw [h2]; ring
      _ = p ^ 5 * (2 * m ^ 2) := by rw [h1]
      _ = (2 * (p ^ 5 * w)) * v := by rw [hm2]; ring
  have key2 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hv) key
  exact ⟨∑ d ∈ (p ^ 5).divisors, d, by rw [← key2]; ring⟩
