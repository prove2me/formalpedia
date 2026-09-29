-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_cyclotomic_pair_coprime
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-29T00:38:59.313324+00:00
-- url     : https://prove2.me/submissions/530e1f01-7963-4f82-93b7-c5f5c24ea813

import Mathlib

theorem solution (p : Nat) (hp2 : p != 2) :
    Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) = 1 := by
  set g := Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) with hg
  have hA : g ∣ p ^ 2 + p + 1 := Nat.gcd_dvd_left _ _
  have hB : g ∣ p ^ 2 - p + 1 := Nat.gcd_dvd_right _ _
  have hle : p ≤ p ^ 2 := by rw [sq]; exact Nat.le_mul_self p
  have hdiff : p ^ 2 + p + 1 = (p ^ 2 - p + 1) + 2 * p := by omega
  have h2p : g ∣ 2 * p := (Nat.dvd_add_right hB).1 (hdiff ▸ hA)
  have hodd : Odd (p ^ 2 + p + 1) := by
    have hev : Even (p ^ 2 + p) := by
      have : p ^ 2 + p = p * (p + 1) := by ring
      rw [this]; exact Nat.even_mul_succ_self p
    exact hev.add_one
  have hg_odd : Odd g := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ p ^ 2 + p + 1 := (even_iff_two_dvd.1 hev).trans hA
    have := Nat.odd_iff.1 hodd
    omega
  have hcop : Nat.Coprime g 2 := Nat.coprime_two_right.2 hg_odd
  have hgp : g ∣ p := hcop.dvd_mul_left.1 h2p
  have hgpp : g ∣ p ^ 2 + p := by
    have : p ^ 2 + p = p * (p + 1) := by ring
    rw [this]; exact Dvd.dvd.mul_right hgp _
  have h1 : g ∣ 1 := (Nat.dvd_add_right hgpp).1 hA
  exact Nat.dvd_one.1 h1
