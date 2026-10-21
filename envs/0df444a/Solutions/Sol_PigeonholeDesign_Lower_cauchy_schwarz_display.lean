-- Prove2me | solution 1 for PigeonholeDesign.Lower.cauchy_schwarz_display
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T12:04:53.338983+00:00
-- url     : https://prove2.me/submissions/e676f0a4-c8d1-43d1-8a9a-c765b141fe5b

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

theorem solution {K : ℕ} (L : Fin K → ℝ) (T : ℕ) (hL : ∀ k, 0 ≤ L k)
    (hS : 0 < ∑ i, L i ^ 2) :
    ∑ k, L k * Real.sqrt (L k ^ 2 / (∑ i, L i ^ 2) * T) =
        Real.sqrt ((∑ k, L k ^ 2) * ∑ k, L k ^ 2 / (∑ i, L i ^ 2) * T) ∧
      Real.sqrt ((∑ k, L k ^ 2) * ∑ k, L k ^ 2 / (∑ i, L i ^ 2) * T) =
        Real.sqrt (T * ∑ k, L k ^ 2) := by
  let S : ℝ := ∑ i, L i ^ 2
  have hSpos : 0 < S := hS
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hallocation : (∑ k, L k ^ 2 / S * (T : ℝ)) = T := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    change S * S⁻¹ * (T : ℝ) = T
    rw [mul_inv_cancel₀ hSne, one_mul]
  have hroot (k : Fin K) : Real.sqrt (L k ^ 2 / S * (T : ℝ)) =
      L k * Real.sqrt ((T : ℝ) / S) := by
    have heq : L k ^ 2 / S * (T : ℝ) = L k ^ 2 * ((T : ℝ) / S) := by ring
    rw [heq, Real.sqrt_mul (sq_nonneg (L k)), Real.sqrt_sq (hL k)]
  have htotal : (∑ k, L k * Real.sqrt (L k ^ 2 / S * (T : ℝ))) =
      Real.sqrt ((T : ℝ) * S) := by
    calc
      (∑ k, L k * Real.sqrt (L k ^ 2 / S * (T : ℝ))) =
          ∑ k, L k ^ 2 * Real.sqrt ((T : ℝ) / S) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hroot]
        ring
      _ = S * Real.sqrt ((T : ℝ) / S) := by rw [← Finset.sum_mul]
      _ = Real.sqrt (S ^ 2) * Real.sqrt ((T : ℝ) / S) := by
        rw [Real.sqrt_sq (le_of_lt hSpos)]
      _ = Real.sqrt (S ^ 2 * ((T : ℝ) / S)) :=
        (Real.sqrt_mul (sq_nonneg S) ((T : ℝ) / S)).symm
      _ = Real.sqrt ((T : ℝ) * S) := by
        congr 1
        field_simp
  change (∑ k, L k * Real.sqrt (L k ^ 2 / S * (T : ℝ))) =
      Real.sqrt (S * ∑ k, L k ^ 2 / S * (T : ℝ)) ∧
    Real.sqrt (S * ∑ k, L k ^ 2 / S * (T : ℝ)) = Real.sqrt ((T : ℝ) * S)
  rw [hallocation]
  constructor
  · rw [htotal, mul_comm S (T : ℝ)]
  · rw [mul_comm S (T : ℝ)]

#print axioms solution
