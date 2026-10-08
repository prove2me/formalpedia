-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_reciprocal_deriv_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T14:28:17.332613+00:00
-- url     : https://prove2.me/submissions/eefc4d60-cbff-4bec-916a-39c7590f37cd

import Mathlib
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) :
    HasDerivAt
      (fun z : ℂ =>
        ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * z) ^ (w i : ℂ))
      (-((∑ i ∈ Finset.range n, w i * a i : ℝ) : ℂ)) 0 := by
  have hfactor : ∀ i ∈ Finset.range n,
      HasDerivAt
        (fun z : ℂ => (1 - (a i : ℂ) * z) ^ (w i : ℂ))
        (-((w i * a i : ℝ) : ℂ)) 0 := by
    intro i hi
    have hlin :
        HasDerivAt (fun z : ℂ => 1 - (a i : ℂ) * z) (-(a i : ℂ)) 0 := by
      simpa using
        (hasDerivAt_const_mul (𝕜 := ℂ) (x := (0 : ℂ)) (a i : ℂ)).const_sub 1
    convert hlin.cpow_const (c := (w i : ℂ)) (by simp) using 1 <;> simp <;> ring
  have hp := HasDerivAt.fun_finsetProd hfactor
  have hcoeff :
      (∑ i ∈ Finset.range n,
        (∏ j ∈ (Finset.range n).erase i,
          (1 - (a j : ℂ) * 0) ^ (w j : ℂ)) •
            (-((w i * a i : ℝ) : ℂ))) =
        -((∑ i ∈ Finset.range n, w i * a i : ℝ) : ℂ) := by
    simp [Complex.ofReal_sum]
  rw [hcoeff] at hp
  exact hp
