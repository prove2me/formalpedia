-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_explicit_dominated_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T09:24:00.21421+00:00
-- url     : https://prove2.me/submissions/3ac793ab-7e5a-4c31-8f19-efc88c36d055

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_norm_real_exponent
open scoped BigOperators

theorem solution (n : ℕ) (b w : ℕ → ℝ) (x ε δ : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖(∏ i ∈ Finset.range n,
        ((b i : ℂ) + ε * Complex.I) ^ (w i : ℂ)) /
        ((x : ℂ) + ε * Complex.I)‖ ≤
      (∏ i ∈ Finset.range n,
        ‖(b i : ℂ) + ε * Complex.I‖ ^ (w i : ℝ)) / δ := by
  rw [norm_div, norm_prod]
  simp_rw [WeightedRootIntegralIdentity.cpow_norm_real_exponent]
  have hreal : x ≤ ‖(x : ℂ) + ε * Complex.I‖ := by
    simpa using (Complex.re_le_norm ((x : ℂ) + ε * Complex.I))
  have hden : δ ≤ ‖(x : ℂ) + ε * Complex.I‖ := le_trans hx hreal
  have hprod : 0 ≤ ∏ i ∈ Finset.range n,
      ‖(b i : ℂ) + ε * Complex.I‖ ^ (w i : ℝ) := by
    positivity
  gcongr
