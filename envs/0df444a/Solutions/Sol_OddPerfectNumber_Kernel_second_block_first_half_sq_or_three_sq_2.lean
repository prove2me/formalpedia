-- Prove2me | solution 2 for OddPerfectNumber.Kernel.second_block_first_half_sq_or_three_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T16:59:30.492679+00:00
-- url     : https://prove2.me/submissions/e0a7af00-1503-4f47-bddd-70f09788b1fa

import Mathlib

namespace P2M_a8a4da03

theorem sq_of_cop {a b e : ℕ} (h : Nat.Coprime a b) (he : a * b = e ^ 2) :
    ∃ d : ℕ, a = d ^ 2 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) he

theorem B_not_sq (k d : ℕ) (hk : 1 ≤ k) (h : 16 * k ^ 2 + 4 * k + 1 = d ^ 2) : False := by
  rcases le_or_gt d (4 * k) with hd | hd
  · have : d ^ 2 ≤ (4 * k) ^ 2 := Nat.pow_le_pow_left hd 2
    nlinarith
  · have hd' : 4 * k + 1 ≤ d := hd
    have : (4 * k + 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hd' 2
    nlinarith

theorem B_ne_three_sq (k w : ℕ) (h : 16 * k ^ 2 + 4 * k + 1 = 3 * w ^ 2) : False := by
  have h4 : (16 * k ^ 2 + 4 * k + 1) % 4 = 1 := by omega
  rw [h] at h4
  have : w % 4 = 0 ∨ w % 4 = 1 ∨ w % 4 = 2 ∨ w % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0 <;>
    simp [Nat.mul_mod, Nat.pow_mod, h0] at h4

theorem main (k c y : ℕ) (hk : 1 ≤ k) (hc : c.Prime)
    (hy : (2 * k + 1) * (16 * k ^ 2 + 4 * k + 1) = c * y ^ 2) :
    (∃ z : ℕ, 2 * k + 1 = z ^ 2) ∨ (∃ z : ℕ, 2 * k + 1 = 3 * z ^ 2) := by
  set A := 2 * k + 1 with hA
  set B := 16 * k ^ 2 + 4 * k + 1 with hB
  have hrel : B + 6 * A = 4 * A ^ 2 + 3 := by rw [hA, hB]; ring
  have hcopc : ∀ x : ℕ, ¬ c ∣ x → Nat.Coprime x c := fun x hx =>
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hc).2 hx))
  by_cases h3 : 3 ∣ A
  · obtain ⟨m, hm⟩ := h3
    -- B = 3 * B1
    have hB3 : B + 18 * m = 36 * m ^ 2 + 3 := by rw [hm] at hrel; nlinarith
    obtain ⟨B1, hB1⟩ : ∃ B1, B1 + 6 * m = 12 * m ^ 2 + 1 := ⟨12 * m ^ 2 + 1 - 6 * m, by
      have : 6 * m ≤ 12 * m ^ 2 + 1 := by nlinarith
      omega⟩
    have hBB1 : B = 3 * B1 := by omega
    have h3B1 : ¬ 3 ∣ B1 := by
      rintro ⟨t, ht⟩
      have : (12 * m ^ 2 + 1) % 3 = 1 := by omega
      omega
    have hcop : Nat.Coprime m B1 := by
      apply Nat.coprime_of_dvd'
      intro q _ hqm hqB
      have h1 : q ∣ B1 + 6 * m := dvd_add hqB (dvd_mul_of_dvd_right hqm 6)
      rw [hB1] at h1
      have h2 : q ∣ 12 * m ^ 2 := by
        rw [pow_two]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hqm _) _
      exact (Nat.dvd_add_right h2).mp h1
    have hy' : 9 * m * B1 = c * y ^ 2 := by rw [← hy, hm, hBB1]; ring
    by_cases hcB : c ∣ B1
    · have hc3 : c ≠ 3 := by rintro rfl; exact h3B1 hcB
      have h3y : 3 ∣ y := by
        have : 3 ∣ c * y ^ 2 := ⟨3 * m * B1, by rw [← hy']; ring⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hc).mp h) (Ne.symm hc3)
        · exact Nat.prime_three.dvd_of_dvd_pow h
      obtain ⟨t, rfl⟩ := h3y
      have hmt : m * (B1 * c) = (c * t) ^ 2 := by
        have : 9 * (m * B1) = 9 * (c * t ^ 2) := by rw [← mul_assoc, hy']; ring
        have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
        rw [← mul_assoc, this]; ring
      have hcopm : Nat.Coprime m (B1 * c) :=
        Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right hcB hcop)
      obtain ⟨d, hd⟩ := sq_of_cop hcopm hmt
      right; exact ⟨d, by rw [hm, hd]⟩
    · exfalso
      have hcop3 : Nat.Coprime B1 3 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3B1)
      have hcop9 : Nat.Coprime B1 9 := by
        have := Nat.Coprime.pow_right 2 hcop3; simpa using this
      have hcopall : Nat.Coprime B1 (9 * m * c) :=
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hcop9 hcop.symm) (hcopc B1 hcB)
      have heq : B1 * (9 * m * c) = (c * y) ^ 2 := by
        have : B1 * (9 * m * c) = (9 * m * B1) * c := by ring
        rw [this, hy']; ring
      obtain ⟨d, hd⟩ := sq_of_cop hcopall heq
      exact B_ne_three_sq k d (by rw [← hB, hBB1, hd])
  · have hcop : Nat.Coprime A B := by
      have hg3 : Nat.gcd A B ∣ 3 := by
        have h1 : Nat.gcd A B ∣ B + 6 * A :=
          dvd_add (Nat.gcd_dvd_right A B) (dvd_mul_of_dvd_right (Nat.gcd_dvd_left A B) 6)
        rw [hrel] at h1
        have h2 : Nat.gcd A B ∣ 4 * A ^ 2 := by
          rw [pow_two]
          exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_left A B) _) _
        exact (Nat.dvd_add_right h2).mp h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hg3 with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_left A B) h3
    by_cases hcA : c ∣ A
    · exfalso
      have hcB : ¬ c ∣ B := fun hcB => by
        have := Nat.dvd_gcd hcA hcB
        rw [hcop] at this
        exact hc.one_lt.ne' (Nat.dvd_one.mp this)
      have hcopall : Nat.Coprime B (A * c) :=
        Nat.Coprime.mul_right hcop.symm (hcopc B hcB)
      have heq : B * (A * c) = (c * y) ^ 2 := by
        have : B * (A * c) = (A * B) * c := by ring
        rw [this, hy]; ring
      obtain ⟨d, hd⟩ := sq_of_cop hcopall heq
      exact B_not_sq k d hk hd
    · have hcopall : Nat.Coprime A (B * c) := Nat.Coprime.mul_right hcop (hcopc A hcA)
      have heq : A * (B * c) = (c * y) ^ 2 := by
        have : A * (B * c) = (A * B) * c := by ring
        rw [this, hy]; ring
      obtain ⟨d, hd⟩ := sq_of_cop hcopall heq
      left; exact ⟨d, hd⟩

end P2M_a8a4da03

theorem solution (p c y : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hc : c.Prime) (hy : ((p + 1) / 2) * (p ^ 2 - p + 1) = c * y ^ 2) :
    (exists z : Nat, (p + 1) / 2 = z ^ 2) ∨ (exists z : Nat, (p + 1) / 2 = 3 * z ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact absurd hp (by norm_num)
    · exact h
  have hA : (4 * k + 1 + 1) / 2 = 2 * k + 1 := by omega
  have hB : (4 * k + 1) ^ 2 - (4 * k + 1) + 1 = 16 * k ^ 2 + 4 * k + 1 := by
    have : (4 * k + 1) ^ 2 = 16 * k ^ 2 + 4 * k + (4 * k + 1) := by ring
    omega
  rw [hA, hB] at hy
  rw [hA]
  exact P2M_a8a4da03.main k c y hk hc hy
