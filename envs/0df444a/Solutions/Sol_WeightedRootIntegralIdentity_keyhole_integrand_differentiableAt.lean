-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_integrand_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T10:56:51.964075+00:00
-- url     : https://prove2.me/submissions/909cfd30-6b10-42d1-9c0f-c018098065c8

import Mathlib
open scoped BigOperators

theorem solution (n : ℕ) (f : ℕ → ℂ → ℂ) (z : ℂ)
    (hz : z ≠ 0)
    (hf : ∀ i ∈ Finset.range n, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun u => (∏ i ∈ Finset.range n, f i u) / u) z := by
  have hp : DifferentiableAt ℂ (fun u => ∏ i ∈ Finset.range n, f i u) z := by
    fun_prop
  fun_prop
