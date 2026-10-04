-- Prove2me | solution 1 for OddPerfectNumber.Kernel.odd_order_source_not_minus_block_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T22:24:15.927975+00:00
-- url     : https://prove2.me/submissions/522c4670-b8e2-422f-91d8-dda3ec404d8e

import Mathlib

theorem solution {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp : p.Prime) (hp4 : p % 4 = 1) (hq : q.Prime) (hqp : q != p)
    (hleg : legendreSym q p = -1) :
    Even (orderOf (q : ZMod p)) := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 : ((p : ℕ) : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod p 2, show p % 2 = 1 by omega]; simp
    have hsq : IsSquare ((p : ℕ) : ZMod 2) := by rw [h1]; exact IsSquare.one
    exact (legendreSym.eq_neg_one_iff' (p := 2)).mp hleg hsq
  rw [legendreSym.quadratic_reciprocity_one_mod_four hp4 hq2] at hleg
  have hns : ¬ IsSquare ((q : ℕ) : ZMod p) := (legendreSym.eq_neg_one_iff' (p := p)).mp hleg
  have hq0 : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h; apply hns; rw [h]; exact ⟨0, by simp⟩
  have hpow : ¬ ((q : ℕ) : ZMod p) ^ (p / 2) = 1 := fun h =>
    hns ((ZMod.euler_criterion p hq0).mpr h)
  have hd : orderOf ((q : ℕ) : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  apply hpow
  apply orderOf_dvd_iff_pow_eq_one.mp
  have h2 : p - 1 = 2 * (p / 2) := by omega
  rw [h2] at hd
  exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) hd
