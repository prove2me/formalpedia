-- Prove2me | solution 1 for Timetabling85.ClassTeacher.remaining_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:03:39.012985+00:00
-- url     : https://prove2.me/submissions/e378a205-99d9-4baa-8cea-2d8cea692bcd

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems



namespace Timetabling85.ClassTeacher

lemma lo_eq (s p : ℕ) : lo s p = s / p := by
  unfold lo; exact Nat.floor_div_eq_div s p

lemma hi_eq (s p : ℕ) (hp : 0 < p) : hi s p = (s + p - 1) / p := by
  unfold hi
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (by exact_mod_cast hp)]
    have h1 := Nat.div_add_mod (s + p - 1) p
    have h2 := Nat.mod_lt (s + p - 1) hp
    have : s ≤ (s + p - 1) / p * p := by
      generalize (s + p - 1) / p = c at *
      rw [Nat.mul_comm c p]
      omega
    exact_mod_cast this
  · have hk : (s : ℚ) / p ≤ ⌈(s : ℚ) / p⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ (by exact_mod_cast hp)] at hk
    have hk' : s ≤ ⌈(s : ℚ) / p⌉₊ * p := by exact_mod_cast hk
    generalize ⌈(s : ℚ) / p⌉₊ = k at *
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hp]
    rw [Nat.succ_mul]
    omega

lemma remaining_core (s y p : ℕ) (hp : 2 ≤ p) (hlo : s / p ≤ y) (hhi : y ≤ (s + p - 1) / p) :
    s / p ≤ (s - y) / (p - 1) ∧ (s - y + (p - 1) - 1) / (p - 1) ≤ (s + p - 1) / p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have e1 : q + 2 - 1 = q + 1 := by omega
  have e2 : s + (q + 2) - 1 = s + q + 1 := by omega
  rw [e1]; rw [e2] at hhi ⊢
  have hp0 : 0 < q + 2 := by omega
  have h1 := Nat.div_add_mod s (q + 2)
  have h2 := Nat.mod_lt s hp0
  have h3 := Nat.div_add_mod (s + q + 1) (q + 2)
  have h4 := Nat.mod_lt (s + q + 1) hp0
  generalize s / (q + 2) = a at *
  generalize (s + q + 1) / (q + 2) = b at *
  generalize s % (q + 2) = r at *
  generalize (s + q + 1) % (q + 2) = r' at *
  have ea : (q + 2) * a = q * a + 2 * a := by ring
  have eb : (q + 2) * b = q * b + 2 * b := by ring
  have hba : b = a ∨ b = a + 1 := by
    have hb1 : b ≤ a + 1 := by
      by_contra hc
      have : q * (a + 2) ≤ q * b := Nat.mul_le_mul_left _ (by omega)
      have e : q * (a + 2) = q * a + 2 * q := by ring
      omega
    have hb2 : a ≤ b := by
      by_contra hc
      have : q * (b + 1) ≤ q * a := Nat.mul_le_mul_left _ (by omega)
      have e : q * (b + 1) = q * b + q := by ring
      omega
    omega
  rcases hba with h | h
  · rw [h] at hhi h3
    rw [h]
    have e3 : a * (q + 1) = q * a + a := by ring
    have e4 : (a + 1) * (q + 1) = q * a + a + q + 1 := by ring
    have hs : s = q * a + 2 * a := by omega
    constructor
    · apply (Nat.le_div_iff_mul_le (by omega)).mpr
      omega
    · apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simp only [Nat.succ_eq_add_one]
      omega
  · rw [h] at hhi h3
    rw [h]
    have e3 : a * (q + 1) = q * a + a := by ring
    have e4 : (a + 1 + 1) * (q + 1) = q * a + a + 2 * q + 2 := by ring
    have e5 : (q + 2) * (a + 1) = q * a + 2 * a + q + 2 := by ring
    constructor
    · apply (Nat.le_div_iff_mul_le (by omega)).mpr
      omega
    · apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simp only [Nat.succ_eq_add_one]
      omega

theorem remaining_bounds_core (s y p : ℕ) (hp : 2 ≤ p) (hlo : lo s p ≤ y) (hhi : y ≤ hi s p) :
    lo s p ≤ lo (s - y) (p - 1) ∧ hi (s - y) (p - 1) ≤ hi s p := by
  rw [lo_eq] at hlo
  rw [hi_eq _ _ (by omega)] at hhi
  rw [lo_eq, lo_eq, hi_eq _ _ (by omega), hi_eq _ _ (by omega)]
  exact remaining_core s y p hp hlo hhi

end Timetabling85.ClassTeacher

open Timetabling85.ClassTeacher


theorem solution (s y p : ℕ) (hp : 2 ≤ p) (hlo : lo s p ≤ y) (hhi : y ≤ hi s p) :
    lo s p ≤ lo (s - y) (p - 1) ∧ hi (s - y) (p - 1) ≤ hi s p := by
  exact remaining_bounds_core s y p hp hlo hhi
