-- Prove2me | solution 1 for RudinSquares.square_positions_24_1_and_8_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T17:36:36.978949+00:00
-- url     : https://prove2.me/submissions/e6664afe-f79e-4c3b-9b90-58b6b443aa8e

import Mathlib
import Definitions.Def_RudinSquares_Defs

open RudinSquares

theorem solution :
    S 24 1 = {n : ℕ | ∃ k : ℤ, (n : ℤ) = GP k} ∧
    S 8 1 = Set.range T := by
  constructor
  · ext n
    simp only [S, IsSq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm⟩
      have hmod : m * m % 6 = 1 := by rw [← hm]; omega
      have hr : m % 6 = 1 ∨ m % 6 = 5 := by
        rw [Int.mul_emod] at hmod
        have h0 : 0 ≤ m % 6 := Int.emod_nonneg _ (by norm_num)
        have h6 : m % 6 < 6 := Int.emod_lt_of_pos _ (by norm_num)
        interval_cases h : m % 6 <;> simp_all
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (6 * k - 1) * (6 * k - 1) = m * m := by
        rcases hr with hr | hr
        · exact ⟨-(m / 6), by
            have : m = 6 * (m / 6) + 1 := by omega
            linear_combination (-(m + 6 * (m / 6) + 1)) * this⟩
        · exact ⟨m / 6 + 1, by
            have : m = 6 * (m / 6) + 5 := by omega
            linear_combination (-(m + 6 * (m / 6) + 5)) * this⟩
      refine ⟨k, ?_⟩
      have h2 : k * (3 * k - 1) = 2 * (n : ℤ) := by nlinarith
      unfold GP
      rw [h2, Int.mul_ediv_cancel_left _ (by norm_num)]
    · rintro ⟨k, hk⟩
      refine ⟨6 * k - 1, ?_⟩
      have hev : k * (3 * k - 1) % 2 = 0 := by
        rw [Int.mul_emod]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · simp [h]
        · have : (3 * k - 1) % 2 = 0 := by omega
          simp [this]
      have h2 : GP k * 2 = k * (3 * k - 1) := by
        unfold GP
        exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hev)
      rw [hk]
      linear_combination (12 : ℤ) * h2
  · ext n
    simp only [S, IsSq, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      have ha : ((m.natAbs * m.natAbs : ℕ) : ℤ) = 8 * (n : ℤ) + 1 := by
        push_cast
        rw [abs_mul_abs_self, hm]
      have ha' : m.natAbs * m.natAbs = 8 * n + 1 := by exact_mod_cast ha
      set a := m.natAbs
      have hodd : a % 2 = 1 := by
        have : a * a % 2 = 1 := by rw [ha']; omega
        rw [Nat.mul_mod] at this
        rcases Nat.mod_two_eq_zero_or_one a with h | h
        · simp [h] at this
        · exact h
      refine ⟨a / 2, ?_⟩
      have heq : a = 2 * (a / 2) + 1 := by omega
      have h2 : (a / 2) * (a / 2 + 1) = 2 * n := by
        rw [heq] at ha'
        nlinarith
      unfold T
      rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
    · rintro ⟨k, rfl⟩
      refine ⟨2 * (k : ℤ) + 1, ?_⟩
      have h2 : T k * 2 = k * (k + 1) := by
        unfold T
        exact Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
      have h2' : ((T k : ℕ) : ℤ) * 2 = (k : ℤ) * (k + 1) := by exact_mod_cast h2
      linear_combination (4 : ℤ) * h2'
