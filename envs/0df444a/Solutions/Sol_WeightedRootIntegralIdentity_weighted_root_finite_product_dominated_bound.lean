-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_finite_product_dominated_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T09:16:03.865578+00:00
-- url     : https://prove2.me/submissions/85809506-f2ed-403b-b188-a352d4e38fc9

import Mathlib
open scoped BigOperators

theorem solution (n : ℕ) (z : ℕ → ℂ) (C : ℕ → ℝ) (w : ℂ) (δ : ℝ)
    (hC : ∀ i ∈ Finset.range n, 0 ≤ C i)
    (hfac : ∀ i ∈ Finset.range n, ‖z i‖ ≤ C i)
    (hδ : 0 < δ) (hden : δ ≤ ‖w‖) :
    ‖(∏ i ∈ Finset.range n, z i) / w‖ ≤
      (∏ i ∈ Finset.range n, C i) / δ := by
  rw [norm_div, norm_prod]
  have hprod : 0 ≤ ∏ i ∈ Finset.range n, C i := by
    exact Finset.prod_nonneg (fun i hi => hC i hi)
  gcongr
  exact hfac _ ‹_›
