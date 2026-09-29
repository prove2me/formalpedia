-- Prove2me | solution 1 for OnlinePrimalDual.Routing.routing_competitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:20:44.270085+00:00
-- url     : https://prove2.me/submissions/56e2be35-ec48-4619-9ea1-06225a37d1d6

import Mathlib

namespace OnlinePrimalDual.Routing

end OnlinePrimalDual.Routing

open OnlinePrimalDual.Routing

theorem solution {J : Type*} [Fintype J]
    (Mcopy accepted : J → ℝ) (M loadPerCopy globalLoad n : ℝ)
    (hper_copy_bandwidth : ∀ j, Mcopy j ≤ accepted j)
    (hquota : M ≤ ∑ j, Mcopy j)
    (hn_pos : 0 < n)
    (hper_copy_load : loadPerCopy ≤ 2 + 6 * Real.logb 2 n)
    (hload_aggregation : globalLoad ≤ 4 * loadPerCopy) :
    M ≤ ∑ j, accepted j ∧ globalLoad ≤ 8 + 24 * Real.logb 2 n := by
  refine ⟨le_trans hquota (Finset.sum_le_sum fun j _ => hper_copy_bandwidth j), ?_⟩
  linarith
