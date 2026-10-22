-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P02.diagonal_inverse_averages
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T06:37:14.300008+00:00
-- url     : https://prove2.me/submissions/b949a05d-c3cb-4e00-a7b3-4c5000dc62a8

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
An independently written coordinate construction for Lemma 1 of
K. R. Parthasarathy, arXiv:1101.5041v1, PDF p.10.
The two entries are d + sqrt(d^2 - 1) and d - sqrt(d^2 - 1).
Their product is one, so taking inverses simply interchanges them.
-/

theorem solution {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    (hd : ∀ j, 1 ≤ d j) :
    ∃ d1 d2 : Fin n → ℝ,
      (∀ j, 0 < d1 j) ∧ (∀ j, 0 < d2 j) ∧
      (∀ j, d j = (d1 j + d2 j) / 2) ∧
      (∀ j, d j = ((d1 j)⁻¹ + (d2 j)⁻¹) / 2) := by
  let s : Fin n → ℝ := fun j => Real.sqrt (d j ^ 2 - 1)
  have hs (j : Fin n) : 0 ≤ s j := Real.sqrt_nonneg _
  have hsq (j : Fin n) : s j ^ 2 = d j ^ 2 - 1 := by
    apply Real.sq_sqrt
    nlinarith [hd j]
  have hplus (j : Fin n) : 0 < d j + s j := by
    linarith [hd j, hs j]
  have hprod (j : Fin n) : (d j + s j) * (d j - s j) = 1 := by
    nlinarith [hsq j]
  have hminus (j : Fin n) : 0 < d j - s j := by
    by_contra h
    have hle : d j - s j ≤ 0 := le_of_not_gt h
    have := mul_nonpos_of_nonneg_of_nonpos (hplus j).le hle
    linarith [hprod j]
  refine ⟨fun j => d j + s j, fun j => d j - s j, hplus, hminus, ?_, ?_⟩
  · intro j
    ring
  · intro j
    have h1 : (d j + s j)⁻¹ = d j - s j := by
      apply inv_eq_of_mul_eq_one_right
      exact hprod j
    have h2 : (d j - s j)⁻¹ = d j + s j := by
      apply inv_eq_of_mul_eq_one_right
      rw [mul_comm]
      exact hprod j
    rw [h1, h2]
    ring

#print axioms solution
