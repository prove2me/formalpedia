-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_product_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:33:21.692183+00:00
-- url     : https://prove2.me/submissions/4cdcd955-8689-4177-a640-1edd2ad6e67f

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_norm_real_exponent
open scoped BigOperators

theorem solution (n : ℕ) (b w : ℕ → ℝ) (ε : ℝ) :
    ‖∏ i ∈ Finset.range n,
      ((b i : ℂ) + ε * Complex.I) ^ (w i : ℂ)‖ =
      ∏ i ∈ Finset.range n,
        ‖(b i : ℂ) + ε * Complex.I‖ ^ (w i : ℝ) := by
  simp_rw [norm_prod, WeightedRootIntegralIdentity.cpow_norm_real_exponent]
