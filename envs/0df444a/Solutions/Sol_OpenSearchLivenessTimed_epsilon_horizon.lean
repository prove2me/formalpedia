-- Prove2me | solution 1 for OpenSearchLivenessTimed.epsilon_horizon
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T18:54:16.564546+00:00
-- url     : https://prove2.me/submissions/0a240e0b-85a3-4749-90cd-16fb0b3ec95f

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

theorem solution (b : ℚ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (allContested : ℕ → ℚ) (hbound : ∀ K, allContested K ≤ b ^ K)
    (ε : ℚ) (hε : 0 < ε) : ∃ K, allContested K < ε := by
  have htendsto := tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1
  -- Note: `apply htendsto.eventually` fails to unify the predicate
  -- metavariable, so give the `∀ᶠ` proof as a term; `y ∈ Iio ε` is
  -- definitionally `y < ε`, so it checks against the stated type.
  have hev : ∀ᶠ n in Filter.atTop, b ^ n < ε :=
    htendsto.eventually (Iio_mem_nhds hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  exact ⟨K, lt_of_le_of_lt (hbound K) (hK K (le_refl K))⟩
