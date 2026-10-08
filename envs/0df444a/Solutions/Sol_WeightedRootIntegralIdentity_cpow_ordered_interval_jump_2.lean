-- Prove2me | solution 2 for WeightedRootIntegralIdentity.cpow_ordered_interval_jump
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T20:56:06.056567+00:00
-- url     : https://prove2.me/submissions/b55f7351-b9cd-451e-ac18-c8ac6fc56a77

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_ordered_interval_boundary
import Theorems.Thm_WeightedRootIntegralIdentity_monotone_on_range_of_adjacent
open scoped BigOperators

theorem solution
    (n k : ℕ) (a w : ℕ → ℝ)
    (hk : k < n - 1)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (x : ℝ) (hxlo : a k < x) (hxhi : x < a (k + 1)) :
    let P : ℂ := ∏ i ∈ Finset.range n, (((a i - x : ℝ) : ℂ) ^ (w i : ℂ))
    let M : ℝ := ∏ i ∈ Finset.range n, Real.rpow |a i - x| (w i)
    let θ : ℝ := Real.pi * (∑ i ∈ Finset.range (k + 1), w i)
    P - star P = ((2 * M * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  dsimp only
  have hEuler (M θ : ℝ) :
      (M : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) -
          star ((M : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        ((2 * M * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    apply Complex.ext <;>
      simp [Complex.sin_ofReal_re, Complex.sin_ofReal_im,
        Complex.cos_ofReal_re, Complex.cos_ofReal_im] <;>
      ring
  have hglobal :=
    WeightedRootIntegralIdentity.monotone_on_range_of_adjacent n a hmono
  rw [WeightedRootIntegralIdentity.cpow_ordered_interval_boundary
    n k a w hk hglobal x hxlo hxhi]
  exact hEuler
    (∏ i ∈ Finset.range n, Real.rpow |a i - x| (w i))
    (Real.pi * (∑ i ∈ Finset.range (k + 1), w i))
