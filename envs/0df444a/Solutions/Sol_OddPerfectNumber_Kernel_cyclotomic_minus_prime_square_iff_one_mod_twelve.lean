-- Prove2me | solution 1 for OddPerfectNumber.Kernel.cyclotomic_minus_prime_square_iff_one_mod_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:13:26.080165+00:00
-- url     : https://prove2.me/submissions/95476221-07e1-42e2-8e23-88dbaf032e65

import Mathlib

set_option autoImplicit false

lemma cycMinusF0c9_order {p q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hqd : q ∣ p ^ 2 - p + 1) :
    (p : ZMod q) ≠ 0 ∧ orderOf (p : ZMod q) = 6 ∧ q % 6 = 1 := by
  have := Fact.mk hq
  have hle : p ≤ p ^ 2 := by
    rcases Nat.eq_zero_or_pos p with h | h
    · simp [h]
    · exact Nat.le_self_pow (by norm_num) p
  have hcast : ((p : ZMod q)) ^ 2 - (p : ZMod q) + 1 = 0 := by
    have h1 : ((p ^ 2 - p + 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hqd
    push_cast [Nat.cast_sub hle] at h1
    exact h1
  have hq2 : q ≠ 2 := by
    rintro rfl
    have he : Even (p * (p - 1)) := Nat.even_mul_pred_self p
    have heq : p ^ 2 - p = p * (p - 1) := by
      rw [Nat.mul_sub_one, pow_two]
    rw [heq] at hqd
    obtain ⟨k, hk⟩ := he
    omega
  set x : ZMod q := (p : ZMod q) with hx
  have h3 : x ^ 3 = -1 := by linear_combination (x + 1) * hcast
  have h6 : x ^ 6 = 1 := by linear_combination (x ^ 3 - 1) * h3
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at h3
    norm_num at h3
  have hn2 : ¬ x ^ 2 = 1 := by
    intro h2
    have hx2 : x = 2 := by linear_combination h2 - hcast
    have h30 : ((3 : ℕ) : ZMod q) = 0 := by
      rw [hx2] at h2
      push_cast
      linear_combination h2
    have := (ZMod.natCast_eq_zero_iff 3 q).mp h30
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp this)
  have hn3 : ¬ x ^ 3 = 1 := by
    intro h1
    have h20 : ((2 : ℕ) : ZMod q) = 0 := by
      push_cast
      linear_combination h3 - h1
    have := (ZMod.natCast_eq_zero_iff 2 q).mp h20
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)
  have hd6 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hnd2 : ¬ orderOf x ∣ 2 := fun h => hn2 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hnd3 : ¬ orderOf x ∣ 3 := fun h => hn3 (orderOf_dvd_iff_pow_eq_one.mp h)
  have ho : orderOf x = 6 := by
    have hmem : orderOf x ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd6, by norm_num⟩
    have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact (hnd2 (by rw [h]; norm_num)).elim
    · exact (hnd2 (by rw [h])).elim
    · exact (hnd3 (by rw [h])).elim
    · exact h
  have hdq : orderOf x ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hx0
  rw [ho] at hdq
  have := hq.two_le
  refine ⟨hx0, ho, ?_⟩
  omega

theorem solution {p q : Nat} [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hq3 : q != 3) (hqp : q != p)
    (hqd : q ∣ p ^ 2 - p + 1) :
    legendreSym q p = 1 ↔ q % 12 = 1 := by
  have hq : q.Prime := Fact.out
  have hq3' : q ≠ 3 := by simpa using hq3
  obtain ⟨hx0, ho, h6⟩ := cycMinusF0c9_order hq hq3' hqd
  have hx0' : ((p : ℤ) : ZMod q) ≠ 0 := by exact_mod_cast hx0
  rw [legendreSym.eq_one_iff q hx0', Int.cast_natCast, ZMod.euler_criterion q hx0,
    ← orderOf_dvd_iff_pow_eq_one, ho]
  omega
