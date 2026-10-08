-- Prove2me | solution 1 for WeightedRootIntegralIdentity.remote_boundary_norm_vanish
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:22:41.328061+00:00
-- url     : https://prove2.me/submissions/cea58abf-cff6-4093-91ef-6c4a9e8eb5b2

import Mathlib
theorem solution (f M : ℝ → ℝ) (hnonneg : ∀ᶠ R in Filter.atTop, 0 ≤ f R) (hbound : ∀ᶠ R in Filter.atTop, f R ≤ M R) (hM : Filter.Tendsto M Filter.atTop (nhds 0)) : Filter.Tendsto f Filter.atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM hnonneg hbound
