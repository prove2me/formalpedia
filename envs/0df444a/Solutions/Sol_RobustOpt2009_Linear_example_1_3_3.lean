-- Prove2me | solution 1 for RobustOpt2009.Linear.example_1_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:44:41.975058+00:00
-- url     : https://prove2.me/submissions/69c0d8d5-0fe4-4f30-b284-8358d1db0e26

import Definitions.Def_RobustOpt2009_Linear_Model

open Matrix
open scoped BigOperators
open RobustOpt2009.Linear

theorem g78l_robust_iff' {n L : ℕ} (D : Data n L) (Z : Set (Fin L → ℝ)) (x : Fin n → ℝ) :
    Robust D Z x ↔ ∀ z ∈ Z, D.a0 ⬝ᵥ x + ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) ≤ D.b0 := by
  unfold Robust
  refine forall₂_congr fun z _ => ?_
  have : ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) = ∑ l, z l * (D.a l ⬝ᵥ x) - ∑ l, z l * D.b l := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
  rw [this]; constructor <;> intro h <;> linarith

theorem solution {n L : ℕ} (D : Data n L) (Ω : ℝ) (hΩ : 0 ≤ Ω)
    (x : Fin n → ℝ) :
    Robust D {z | Real.sqrt (∑ l, (z l) ^ 2) ≤ Ω} x ↔
      D.a0 ⬝ᵥ x + Ω * Real.sqrt (∑ l, (D.a l ⬝ᵥ x - D.b l) ^ 2) ≤ D.b0 := by
  rw [g78l_robust_iff']
  set c : Fin L → ℝ := fun l => D.a l ⬝ᵥ x - D.b l with hc
  set N := Real.sqrt (∑ l, c l ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  constructor
  · intro h
    rcases hN0.lt_or_eq with hNp | hNz
    · have := h (fun l => Ω / N * c l) (by
        simp only [Set.mem_setOf_eq]
        have : ∑ l, (Ω / N * c l) ^ 2 = (Ω / N) ^ 2 * ∑ l, c l ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hΩ hNp.le), ← hN,
          div_mul_cancel₀ _ hNp.ne'])
      have e : ∑ l, Ω / N * c l * c l = Ω * N := by
        have : ∑ l, Ω / N * c l * c l = Ω / N * ∑ l, c l ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, ← Real.sq_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg (c l)), ← hN]
        field_simp
      simp only [hc] at this e
      rw [e] at this
      exact this
    · have := h 0 (by simp [hΩ])
      rw [← hNz]; simpa using this
  · intro h z hz
    refine le_trans ?_ h
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ z c
    have h2 : Real.sqrt (∑ l, z l ^ 2) * N ≤ Ω * N := mul_le_mul_of_nonneg_right hz hN0
    simp only [hc] at h1 h2 ⊢
    linarith
