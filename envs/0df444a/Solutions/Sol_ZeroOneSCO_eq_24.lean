-- Prove2me | solution 1 for ZeroOneSCO.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:41:08.917221+00:00
-- url     : https://prove2.me/submissions/91801acf-e0ab-4e11-bd08-f0d59f380865

import Mathlib
import Definitions.Def_ZeroOneSCO_Columns

namespace Aux_ZOSeq24

theorem entry (τ : ℝ) (hτ : 0 < τ) (z w : ℝ) :
    (z ≤ 0 ∧ 0 ≤ w ∧ z * w = 0) ↔ min (z + τ * w) 0 = z := by
  constructor
  · rintro ⟨hz, hw, hzw⟩
    rcases mul_eq_zero.mp hzw with h | h
    · rw [h, zero_add, min_eq_right (mul_nonneg hτ.le hw)]
    · rw [h, mul_zero, add_zero, min_eq_left hz]
  · intro h
    have hz : z ≤ 0 := by rw [← h]; exact min_le_right _ _
    rcases le_or_gt (z + τ * w) 0 with h1 | h1
    · rw [min_eq_left h1] at h
      have h2 : τ * w = 0 := by linarith
      have hw : w = 0 := (mul_eq_zero.mp h2).resolve_left hτ.ne'
      exact ⟨hz, hw.ge, by rw [hw, mul_zero]⟩
    · rw [min_eq_right h1.le] at h
      refine ⟨hz, by nlinarith, by rw [← h, zero_mul]⟩

theorem entry_max (τ : ℝ) (hτ : 0 < τ) (z w : ℝ) (h : z ≤ 0 ∧ 0 ≤ w ∧ z * w = 0) :
    max (z + τ * w) 0 = τ * w := by
  obtain ⟨hz, hw, hzw⟩ := h
  rcases mul_eq_zero.mp hzw with h | h
  · rw [h, zero_add, max_eq_left (mul_nonneg hτ.le hw)]
  · rw [h, mul_zero, add_zero, max_eq_right hz]

end Aux_ZOSeq24

open ZeroOneSCO Aux_ZOSeq24 in
theorem solution {M N : ℕ} (Z W : Mat M N) (τ : ℝ) (hτ : 0 < τ) (n : Fin N) :
    ((∀ m, Z m n ≤ 0 ∧ 0 ≤ W m n ∧ Z m n * W m n = 0) ↔
        ∀ m, min (Z m n + τ * W m n) 0 = Z m n) ∧
      ((∀ m, Z m n ≤ 0 ∧ 0 ≤ W m n ∧ Z m n * W m n = 0) →
        colPosNorm (Z + τ • W) n = τ * colNorm W n) := by
  refine ⟨forall_congr' (fun m => entry τ hτ (Z m n) (W m n)), fun h => ?_⟩
  unfold colPosNorm colNorm
  have hs : ∑ m, (max ((Z + τ • W) m n) 0) ^ 2 = τ ^ 2 * ∑ m, (W m n) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, entry_max τ hτ _ _ (h m)]
    ring
  rw [hs, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ.le]
