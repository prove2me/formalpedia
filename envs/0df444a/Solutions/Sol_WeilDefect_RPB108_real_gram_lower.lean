-- Prove2me | solution 1 for WeilDefect.RPB108.real_gram_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:58:57.055623+00:00
-- url     : https://prove2.me/submissions/5c0070bc-cd8c-4662-8b11-e40ece68cf85

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

namespace WeilDefect.RPB108
lemma bounded_cross_lower (a u t : ℝ) (ha : |a| ≤ u) : -u*|t| ≤ a*t := by
  have h : |a*t| ≤ u*|t| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hn := neg_abs_le (a*t)
  linarith
end WeilDefect.RPB108

theorem solution (A : Fin 3 → Fin 3 → ℝ) (d u : Fin 3 → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, d i ≤ A i i)
    (ha : ∀ i j, i ≠ j → |A i j| ≤ offWeights u i j)
    (x : Fin 3 → ℝ) :
    (∑ i, rowMargins d u i*(x i)^2) ≤ realGram A x := by
  have hp01 := mul_nonneg (hu 0) (sq_nonneg (|x 0|-|x 1|))
  have hp02 := mul_nonneg (hu 1) (sq_nonneg (|x 0|-|x 2|))
  have hp12 := mul_nonneg (hu 2) (sq_nonneg (|x 1|-|x 2|))
  have hx0 := sq_abs (x 0)
  have hx1 := sq_abs (x 1)
  have hx2 := sq_abs (x 2)
  simp only [sub_sq, hx0, hx1, hx2] at hp01 hp02 hp12
  have hdi (i : Fin 3) := mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (x i))
  have hc (i j : Fin 3) (hij : i ≠ j) :=
    bounded_cross_lower (A i j) (offWeights u i j) (x i*x j) (ha i j hij)
  have hc01 := hc 0 1 (by decide)
  have hc10 := hc 1 0 (by decide)
  have hc02 := hc 0 2 (by decide)
  have hc20 := hc 2 0 (by decide)
  have hc12 := hc 1 2 (by decide)
  have hc21 := hc 2 1 (by decide)
  simp [offWeights, abs_mul] at hc01 hc10 hc02 hc20 hc12 hc21
  simp [rowMargins, realGram, Fin.sum_univ_succ]
  nlinarith [hdi 0, hdi 1, hdi 2]
