-- Prove2me | solution 1 for TwoConnSS.theorem_5_1_comparison
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:23:22.83146+00:00
-- url     : https://prove2.me/submissions/60d488d2-9c63-4ad6-8380-ad905d3e8512

import Mathlib

theorem solution (m4 mNe4 mMerged opt a b₁ b₂ : ℕ) (hS₀ : 0 < m4 + mNe4)
    (hmerged : mMerged ≤ m4) (hopt : m4 + mNe4 ≤ opt)
    (ha : (a : ℚ) ≤ 5 / 4 * m4 + 16 / 13 * mNe4 - 2)
    (hb₁ : (b₁ : ℚ) ≤ 6 / 5 * mMerged + 5 / 4 * ((m4 : ℚ) - mMerged) + 67 / 50 * mNe4 - 2)
    (hb₂ : (b₂ : ℚ) ≤ opt + mMerged + mNe4 - 1) :
    (let x : ℚ := (mNe4 : ℚ) / ((m4 + mNe4 : ℕ) : ℚ)
     let y : ℚ := (mMerged : ℚ) / ((m4 + mNe4 : ℕ) : ℚ)
     ((min (min a b₁) b₂ : ℕ) : ℚ) / (opt : ℚ) ≤
       min (min (5 / 4 - x / 52) (5 / 4 + 9 * x / 100 - y / 20)) (1 + x + y)) ∧
    (∀ x y : ℚ, 728 / 833 * (5 / 4 - x / 52) + 100 / 833 * (5 / 4 + 9 * x / 100 - y / 20) +
      5 / 833 * (1 + x + y) = 1040 / 833) ∧
    ((min (min a b₁) b₂ : ℕ) : ℚ) ≤ 1040 / 833 * (opt : ℚ) := by
  have hSpos : (0 : ℚ) < (m4 : ℚ) + mNe4 := by exact_mod_cast hS₀
  have hoptQ : (m4 : ℚ) + mNe4 ≤ opt := by exact_mod_cast hopt
  have hoptpos : (0 : ℚ) < opt := lt_of_lt_of_le hSpos hoptQ
  have hmQ : (mMerged : ℚ) ≤ m4 := by exact_mod_cast hmerged
  have h1 : ((min (min a b₁) b₂ : ℕ) : ℚ) ≤ a :=
    Nat.cast_le.mpr ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ((min (min a b₁) b₂ : ℕ) : ℚ) ≤ b₁ :=
    Nat.cast_le.mpr ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ((min (min a b₁) b₂ : ℕ) : ℚ) ≤ b₂ := Nat.cast_le.mpr (min_le_right _ _)
  have hm0 : (0 : ℚ) ≤ mNe4 := Nat.cast_nonneg _
  have hmm0 : (0 : ℚ) ≤ mMerged := Nat.cast_nonneg _
  have hm40 : (0 : ℚ) ≤ m4 := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    have hS : ((m4 + mNe4 : ℕ) : ℚ) = (m4 : ℚ) + mNe4 := Nat.cast_add m4 mNe4
    have hxdef : x = (mNe4 : ℚ) / ((m4 + mNe4 : ℕ) : ℚ) := rfl
    have hydef : y = (mMerged : ℚ) / ((m4 + mNe4 : ℕ) : ℚ) := rfl
    have hxS : x * ((m4 : ℚ) + mNe4) = mNe4 := by
      rw [hxdef, hS]; exact div_mul_cancel₀ _ hSpos.ne'
    have hyS : y * ((m4 : ℚ) + mNe4) = mMerged := by
      rw [hydef, hS]; exact div_mul_cancel₀ _ hSpos.ne'
    have hx0 : 0 ≤ x := by rw [hxdef, hS]; positivity
    have hy0 : 0 ≤ y := by rw [hydef, hS]; positivity
    have hx1 : x ≤ 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_lt_mul_of_pos_right hc hSpos]
    have hy1 : y ≤ 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_lt_mul_of_pos_right hc hSpos]
    have e1 : (0 : ℚ) ≤ 5 / 4 - x / 52 := by linarith
    have e2 : (0 : ℚ) ≤ 5 / 4 + 9 * x / 100 - y / 20 := by linarith
    have e3 : (0 : ℚ) ≤ x + y := by linarith
    refine le_min (le_min ?_ ?_) ?_
    · rw [div_le_iff₀ hoptpos]
      nlinarith [mul_le_mul_of_nonneg_left hoptQ e1]
    · rw [div_le_iff₀ hoptpos]
      nlinarith [mul_le_mul_of_nonneg_left hoptQ e2]
    · rw [div_le_iff₀ hoptpos]
      nlinarith [mul_le_mul_of_nonneg_left hoptQ e3]
  · intro x y
    ring
  · linarith
