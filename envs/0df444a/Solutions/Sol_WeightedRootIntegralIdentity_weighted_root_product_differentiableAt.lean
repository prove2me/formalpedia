-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_product_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T10:31:28.849044+00:00
-- url     : https://prove2.me/submissions/a9fcb471-7226-4cc8-88bb-3c068c9dd847

import Mathlib
open scoped BigOperators

theorem solution (n : ℕ) (f : ℕ → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ Finset.range n, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun u => ∏ i ∈ Finset.range n, f i u) z := by
  fun_prop
