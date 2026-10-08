-- Prove2me | solution 1 for WeightedRootIntegralIdentity.vertical_side_vanish
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:25:02.098785+00:00
-- url     : https://prove2.me/submissions/658f0464-18f9-4f71-9760-6dd169fed4ad

import Mathlib
theorem solution (f M : ℝ → ℝ) (hnonneg : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), 0 ≤ f ε) (hbound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), f ε ≤ M ε) (hM : Filter.Tendsto M (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM hnonneg hbound
