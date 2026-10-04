-- Prove2me | solution 1 for SennottDP.Discounted.finite_horizon_cost_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:23:20.414031+00:00
-- url     : https://prove2.me/submissions/05138e81-ca5c-42a3-a551-2cdad3d68f08

import Mathlib
import Definitions.Def_SennottDP_Discounted_Criteria

open scoped ENNReal NNReal
open Filter Topology

open SennottDP.Discounted Filter Topology NNReal ENNReal in
theorem solution {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (θ : Policy M) (i : S) :
    Monotone (fun n : ℕ => finiteHorizonCost M θ α n i) ∧
      Tendsto (fun n : ℕ => finiteHorizonCost M θ α n i) atTop
        (𝓝 (discountedCost M θ α i)) := by
  refine ⟨?_, ?_⟩
  · intro m n hmn
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hmn)
  · exact ENNReal.tendsto_nat_tsum _
