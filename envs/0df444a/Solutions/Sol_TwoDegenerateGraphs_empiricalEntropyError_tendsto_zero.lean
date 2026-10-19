-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalEntropyError_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/9fb479e6-3ef7-4c83-b6fc-7e91c1a8f0fe

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Filter.Tendsto empiricalEntropyError Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun L : ℕ => 1 / (L : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfirst :
      Filter.Tendsto
        (fun L : ℕ => (1 + logTwo 3) / (L : ℝ))
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℕ => 1 + logTwo 3)
          Filter.atTop (nhds (1 + logTwo 3)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hentropy :
      Filter.Tendsto
        (fun L : ℕ => binaryEntropy (1 / (L : ℝ)))
        Filter.atTop (nhds 0) := by
    have hcontinuous := binaryEntropy_continuous.continuousAt.tendsto.comp hinv
    rw [binaryEntropy_zero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with L
    rfl
  change Filter.Tendsto
    (fun L : ℕ => (1 + logTwo 3) / (L : ℝ) +
      binaryEntropy (1 / (L : ℝ)) / 2)
    Filter.atTop (nhds 0)
  simpa using hfirst.add (hentropy.div_const 2)
end TwoDegenerateGraphs
