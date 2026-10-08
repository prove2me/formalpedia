-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_canonical_absurd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:53:37.111232+00:00
-- url     : https://prove2.me/submissions/3cb3fbb8-6a61-4ebd-a851-5fd9324c288d

import Mathlib

namespace C7680faeAux

theorem geom (x k : ℕ) (hx : 1 ≤ x) :
    (x - 1) * ∑ i ∈ Finset.range k, x ^ i + 1 = x ^ k := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ, ← ih]
    ring

theorem key (x n : ℕ) (h : ∀ j < 44, x * (x ^ 2) ^ j % 89 ≠ 1) :
    ¬ 89 ∣ ∑ i ∈ Finset.range (2 * n + 1), x ^ i := by
  intro hd
  have : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have h0 : ((∑ i ∈ Finset.range (2 * n + 1), x ^ i : ℕ) : ZMod 89) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at h0
  have hg := geom_sum_mul (x : ZMod 89) (2 * n + 1)
  rw [h0, zero_mul] at hg
  have h1 : (x : ZMod 89) ^ (2 * n + 1) = 1 := (sub_eq_zero.1 hg.symm)
  have hx0 : (x : ZMod 89) ≠ 0 := by
    intro hx; rw [hx, zero_pow (by omega)] at h1; exact zero_ne_one h1
  have h88 : (x : ZMod 89) ^ 88 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have e1 : 2 * n + 1 = (2 * (n % 44) + 1) + 88 * (n / 44) := by omega
  rw [e1, pow_add, pow_mul, h88, one_pow, mul_one] at h1
  have h3 : ((x * (x ^ 2) ^ (n % 44) : ℕ) : ZMod 89) = ((1 : ℕ) : ZMod 89) := by
    push_cast
    rw [← pow_mul, ← pow_succ']
    exact h1
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  exact h (n % 44) (Nat.mod_lt _ (by norm_num)) (by simpa using h3)

theorem small_ok (q : ℕ) (hq : q.Prime) (hle : q ≤ 55) (h2 : q ≠ 2) :
    ∀ j < 44, q * (q ^ 2) ^ j % 89 ≠ 1 := by
  interval_cases q <;> first | decide | exact absurd rfl h2 | exact absurd hq (by norm_num)

theorem odd_geom (x n : ℕ) (hx : Odd x) : Odd (∑ i ∈ Finset.range (2 * n + 1), x ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    exact (ih.add_odd hx.pow).add_odd hx.pow

end C7680faeAux

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4.Prime) (hqa : Even (2*a)) (hqb : Even (2*b)) (hqc : Even (2*c)) (hqe : Even (2*e)) : False := by
  subst hD hp_eq
  norm_num at hrel
  rw [hfac, hsigma] at hrel
  have h89 : 89 ∣ (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)
      * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) := by
    have : 89 ∣ 45 * ((∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)
      * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) :=
      hrel ▸ dvd_mul_right _ _
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
  have hp : Nat.Prime 89 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).1 h89 with h | hq
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact C7680faeAux.key 3 a (by decide) h
      · exact C7680faeAux.key 5 b (by decide) h
    · exact C7680faeAux.key 29 c (by decide) h
  -- abundance bound: q4 ≤ 55
  have hq2 := hq4.two_le
  have hle : q4 ≤ 55 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, rfl⟩ : ∃ y, q4 = y + 1 := ⟨q4 - 1, by omega⟩
    have g3 := C7680faeAux.geom 3 (2*a+1) (by norm_num)
    have g5 := C7680faeAux.geom 5 (2*b+1) (by norm_num)
    have g29 := C7680faeAux.geom 29 (2*c+1) (by norm_num)
    have gq := C7680faeAux.geom (y+1) (2*e+1) (by omega)
    norm_num at g3 g5 g29
    simp only [Nat.add_sub_cancel] at gq
    rw [pow_succ] at g3 g5 g29 gq
    set S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
    set S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
    set S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
    set Sq := ∑ i ∈ Finset.range (2*e + 1), (y+1) ^ i
    set Q := (y + 1) ^ (2*e)
    have i3 : 2 * S3 < 3 ^ (2*a) * 3 := by omega
    have i5 : 4 * S5 < 5 ^ (2*b) * 5 := by omega
    have i29 : 28 * S29 < 29 ^ (2*c) * 29 := by omega
    have iq : 55 * Sq < 56 * Q := by
      by_contra hc
      push Not at hc
      have k1 := Nat.mul_le_mul_left y hc
      have k2 := Nat.mul_le_mul_right Q (show 55 ≤ y by omega)
      nlinarith
    have hprod : (2 * S3) * (4 * S5) * (28 * S29) * (55 * Sq)
        < (3 ^ (2*a) * 3) * (5 ^ (2*b) * 5) * (29 ^ (2*c) * 29) * (56 * Q) := by
      apply mul_lt_mul'' _ iq (Nat.zero_le _) (Nat.zero_le _)
      apply mul_lt_mul'' _ i29 (Nat.zero_le _) (Nat.zero_le _)
      exact mul_lt_mul'' i3 i5 (Nat.zero_le _) (Nat.zero_le _)
    have hM : 0 ≤ 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * Q := Nat.zero_le _
    nlinarith
  -- finite check
  rcases eq_or_ne q4 2 with rfl | hne
  swap
  · exact C7680faeAux.key q4 e (C7680faeAux.small_ok q4 hq4 hle hne) hq
  -- q4 = 2 : parity
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; norm_num at hq
  have g2 := C7680faeAux.geom 2 (2*e+1) (by norm_num)
  norm_num at g2
  rw [pow_succ] at g2
  have hS2 : Odd (∑ i ∈ Finset.range (2*e + 1), 2 ^ i) := by
    rw [Nat.odd_iff]; omega
  have hL : Odd (45 * ((∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)
      * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), 2 ^ i))) :=
    Nat.odd_mul.2 ⟨by decide, Nat.odd_mul.2 ⟨Nat.odd_mul.2 ⟨Nat.odd_mul.2
      ⟨C7680faeAux.odd_geom 3 a (by decide), C7680faeAux.odd_geom 5 b (by decide)⟩, C7680faeAux.odd_geom 29 c (by decide)⟩, hS2⟩⟩
  have hR : Even (89 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * 2 ^ (2*e))) :=
    ((Nat.even_pow.2 ⟨even_two, by omega⟩).mul_left _).mul_left _
  rw [hrel] at hL
  exact (Nat.not_even_iff_odd.2 hL) hR
