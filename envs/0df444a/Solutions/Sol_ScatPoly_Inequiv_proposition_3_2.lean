-- Prove2me | solution 1 for ScatPoly.Inequiv.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:52:03.84945+00:00
-- url     : https://prove2.me/submissions/761dc8d8-b5eb-4c23-9b85-cb0223600ab7

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

set_option autoImplicit false
open ScatPoly.Inequiv

theorem spi_neg_one_ne (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp : Odd p) :
    (-1 : F) ≠ 1 := by
  intro h
  have h2 : ((2 : ℕ) : F) = 0 := by
    have : (2 : F) = 0 := by linear_combination -h
    exact_mod_cast this
  rw [CharP.cast_eq_zero_iff F p] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have hp2 := (Fact.out : p.Prime).two_le
  have : p = 2 := by omega
  rcases hp with ⟨c, hc⟩
  omega

theorem spi_partA (F : Type*) [Field F] (p q t : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hqodd : Odd q) (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    h ^ (q ^ 2 + 1) ≠ 1 := by
  intro H1
  have hn1 := spi_neg_one_ne F p hp
  have hne : h ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hh
    have : (1 : F) = 0 := by linear_combination hh
    exact one_ne_zero this
  have hq2 : h ^ (q ^ 2) = h⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]; exact H1
  have step : ∀ j : ℕ, h ^ (q ^ (j + 2)) = (h ^ (q ^ j))⁻¹ := by
    intro j
    rw [show q ^ (j + 2) = q ^ 2 * q ^ j by ring, pow_mul, hq2, inv_pow]
  have step4 : ∀ j : ℕ, h ^ (q ^ (j + 4)) = h ^ (q ^ j) := by
    intro j
    rw [show j + 4 = (j + 2) + 2 by ring, step (j + 2), step j, inv_inv]
  have key : ∀ a b : ℕ, h ^ (q ^ (4 * a + b)) = h ^ (q ^ b) := by
    intro a
    induction a with
    | zero => intro b; simp
    | succ a ih =>
      intro b
      rw [show 4 * (a + 1) + b = (4 * a + b) + 4 by ring, step4, ih]
  obtain ⟨u, hu⟩ := hqodd
  have hQ : h ^ (q ^ t) * h = -1 := by rw [← pow_succ]; exact hh
  have ht : t = 4 * (t / 4) + t % 4 := (Nat.div_add_mod t 4).symm
  have hkey := key (t / 4) (t % 4)
  rw [← ht] at hkey
  rw [hkey] at hQ
  have hmod : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hq2' : q ^ 2 + 1 = 2 * (2 * u ^ 2 + 2 * u + 1) := by rw [hu]; ring
  have hw : (h ^ 2) ^ (2 * u ^ 2 + 2 * u + 1) = 1 := by rw [← pow_mul, ← hq2']; exact H1
  interval_cases hb : t % 4
  · -- t % 4 = 0
    simp only [pow_zero, pow_one] at hQ
    have hh2 : h ^ 2 = -1 := by rw [pow_two]; exact hQ
    rw [hh2] at hw
    have : (-1 : F) ^ (2 * u ^ 2 + 2 * u + 1) = -1 := by
      rw [show 2 * u ^ 2 + 2 * u + 1 = 2 * (u ^ 2 + u) + 1 by ring, pow_succ, pow_mul]; simp
    rw [this] at hw
    exact hn1 hw
  · -- t % 4 = 1
    simp only [pow_one] at hQ
    have hq1 : (h ^ 2) ^ (u + 1) = -1 := by
      rw [← pow_mul, show 2 * (u + 1) = q + 1 by rw [hu]; ring, pow_succ]; exact hQ
    have hw1 : h ^ 2 = 1 := by
      have : (h ^ 2) ^ (2 * u ^ 2 + 2 * u + 1) = ((h ^ 2) ^ (u + 1)) ^ (2 * u) * h ^ 2 := by
        rw [show 2 * u ^ 2 + 2 * u + 1 = (u + 1) * (2 * u) + 1 by ring, pow_succ, pow_mul]
      rw [this, hq1, pow_mul] at hw
      simpa using hw
    rw [hw1] at hq1
    simp at hq1
    exact hn1 hq1.symm
  · -- t % 4 = 2
    have : h ^ (q ^ 2) = h⁻¹ := hq2
    rw [this, inv_mul_cancel₀ hne] at hQ
    exact hn1 hQ.symm
  · -- t % 4 = 3
    have h3 : h ^ (q ^ 3) = (h ^ (q ^ 1))⁻¹ := step 1
    rw [h3] at hQ
    simp only [pow_one] at hQ
    have hqh : h ^ q = -h := by
      have h1 : (h ^ q)⁻¹ * h = -1 := hQ
      have hq' : h ^ q ≠ 0 := pow_ne_zero _ hne
      field_simp at h1
      linear_combination h1
    have hu1 : (h ^ 2) ^ u = -1 := by
      have : h ^ q = h * h ^ (2 * u) := by rw [hu, pow_succ, mul_comm]
      rw [this] at hqh
      have h4 : h * h ^ (2 * u) = h * (-1) := by rw [hqh]; ring
      have := mul_left_cancel₀ hne h4
      rw [← pow_mul]; simpa using this
    have hw1 : h ^ 2 = 1 := by
      have : (h ^ 2) ^ (2 * u ^ 2 + 2 * u + 1) = ((h ^ 2) ^ u) ^ (2 * u + 2) * h ^ 2 := by
        rw [show 2 * u ^ 2 + 2 * u + 1 = u * (2 * u + 2) + 1 by ring, pow_succ, pow_mul]
      rw [this, hu1, Even.neg_one_pow ⟨u + 1, by ring⟩] at hw
      simpa using hw
    rw [hw1] at hu1
    simp at hu1
    exact hn1 hu1.symm

theorem spi_prop_3_2 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    h ^ (q ^ 2 + 1) ≠ 1 ∧ h ^ q ^ (3 * t - 2) ≠ -h := by
  have hqodd : Odd q := by rw [hq]; exact hp.pow
  have hA := spi_partA F p q t hp hqodd h hh
  refine ⟨hA, ?_⟩
  intro hB
  apply hA
  have hne : h ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hh
    have : (1 : F) = 0 := by linear_combination hh
    exact one_ne_zero this
  have hfrob : h ^ (q ^ (2 * t)) = h := by
    rw [← hcard]; exact FiniteField.pow_card h
  have e1 : (h ^ (q ^ (3 * t - 2))) ^ (q ^ 2) = h ^ (q ^ t) := by
    rw [← pow_mul, ← pow_add, show 3 * t - 2 + 2 = 2 * t + t by omega, pow_add, pow_mul, hfrob]
  rw [hB, Odd.neg_pow (hqodd.pow)] at e1
  have e2 : h ^ (q ^ t) = -h⁻¹ := by
    have : h ^ (q ^ t) * h = -1 := by rw [← pow_succ]; exact hh
    field_simp
    linear_combination this
  rw [e2] at e1
  have e3 : h ^ (q ^ 2) = h⁻¹ := by linear_combination -e1
  rw [pow_succ, e3, inv_mul_cancel₀ hne]

theorem solution (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    h ^ (q ^ 2 + 1) ≠ 1 ∧ h ^ q ^ (3 * t - 2) ≠ -h := spi_prop_3_2 F p r t q hp hr hq ht hcard h hh
