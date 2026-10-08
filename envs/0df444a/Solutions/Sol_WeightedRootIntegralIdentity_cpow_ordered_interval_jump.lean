-- Prove2me | solution 1 for WeightedRootIntegralIdentity.cpow_ordered_interval_jump
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:56:06.405083+00:00
-- url     : https://prove2.me/submissions/310e3d90-a570-4190-8f29-bf546a5cdb7e

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_ordered_interval_boundary
import Theorems.Thm_WeightedRootIntegralIdentity_monotone_on_range_of_adjacent
open scoped BigOperators

private theorem real_phase_jump (M θ : ℝ) :
    (M : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) -
      star ((M : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      ((2 * M * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sin_ofReal_re] <;> ring

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
  have hglobal :=
    WeightedRootIntegralIdentity.monotone_on_range_of_adjacent n a hmono
  rw [WeightedRootIntegralIdentity.cpow_ordered_interval_boundary
    n k a w hk hglobal x hxlo hxhi]
  exact real_phase_jump _ _

#print axioms solution
