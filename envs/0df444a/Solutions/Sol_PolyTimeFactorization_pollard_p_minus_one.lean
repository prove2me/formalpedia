-- Prove2me | solution 1 for PolyTimeFactorization.pollard_p_minus_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:07:59.037206+00:00
-- url     : https://prove2.me/submissions/603f9469-c832-4d8a-9a3f-f6e46c3e9881

import Mathlib
namespace PolyTimeFactorization

theorem pollard_p_minus_one (n p a B : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (ha : 1 < a) (hpa : ¬ p ∣ a) (hB : 1 ≤ B)
    (hsmooth : p - 1 ∣ (Finset.Icc 1 B).lcm id) :
    p ∣ Nat.gcd (a ^ (Finset.Icc 1 B).lcm id - 1) n := by
  refine Nat.dvd_gcd ?_ hpn
  obtain ⟨c, hc⟩ := hsmooth
  haveI := Fact.mk hp
  have hpos : 1 ≤ a ^ (Finset.Icc 1 B).lcm id := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos]
  have ha0 : (a : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hf := ZMod.pow_card_sub_one_eq_one ha0
  rw [hc]
  push_cast
  rw [pow_mul, hf, one_pow, sub_self]

end PolyTimeFactorization

theorem solution (n p a B : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (ha : 1 < a) (hpa : ¬ p ∣ a) (hB : 1 ≤ B)
    (hsmooth : p - 1 ∣ (Finset.Icc 1 B).lcm id) :
    p ∣ Nat.gcd (a ^ (Finset.Icc 1 B).lcm id - 1) n :=
  PolyTimeFactorization.pollard_p_minus_one n p a B hp hpn ha hpa hB hsmooth
