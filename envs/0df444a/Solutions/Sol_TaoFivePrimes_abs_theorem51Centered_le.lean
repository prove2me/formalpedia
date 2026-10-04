-- Prove2me | solution 1 for TaoFivePrimes.abs_theorem51Centered_le
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:02:36.997666+00:00
-- url     : https://prove2.me/submissions/bcf88edf-afc0-4b16-b80c-5cd2f4fae8cc

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes

namespace TaoGB

/-- **Tao, the bound following Lemma 4.11.**  The centred divisor coefficient
`g(w) = ∑_{b|w, b>V} Λ(b) − ½ log w` satisfies `|g(w)| ≤ ½ log w`. -/
theorem g_bound (V : ℝ) (w : ℕ) : |theorem51Centered V w| ≤ (1/2) * Real.log w := by
  unfold theorem51Centered
  set A : ℝ := ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
    ArithmeticFunction.vonMangoldt b with hA
  have hnn : 0 ≤ A := Finset.sum_nonneg (fun b _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hle : A ≤ Real.log w := by
    rw [hA, ← ArithmeticFunction.vonMangoldt_sum (n := w)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  rw [abs_le]
  constructor <;> linarith

end TaoGB

theorem solution (V : ℝ) (w : ℕ) :
    |TaoFivePrimes.theorem51Centered V w| ≤ (1/2) * Real.log w :=
  TaoGB.g_bound V w
