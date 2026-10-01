-- Prove2me | solution 1 for OddPerfectNumber.Kernel.fermat_prime_dvd_geom_sum_odd_of_even_pow
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:08:33.23381+00:00
-- url     : https://prove2.me/submissions/26fed9bd-f941-4622-93a7-c205da6a57c2

import Mathlib

theorem solution (p t e : Nat) (hp : p.Prime)
    (ht0 : p ∣ t) (hpm1 : ∃ k, p - 1 = 2 ^ k)
    (hdvd : p ∣ ∑ i ∈ Finset.range (2 * e + 1), t ^ i) :
    p ∣ 2 * e + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht : (t : ZMod p) = 0 := by exact_mod_cast (ZMod.natCast_eq_zero_iff t p).mpr ht0
  have hs : ((∑ i ∈ Finset.range (2*e+1), t^i : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  simp only [Nat.cast_sum, Nat.cast_pow] at hs
  rw [Finset.sum_range_succ'] at hs
  simp [ht] at hs

