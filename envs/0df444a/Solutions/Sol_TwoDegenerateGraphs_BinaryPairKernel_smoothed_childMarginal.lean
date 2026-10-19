-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.smoothed_childMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/c929c6c9-535b-4f8f-8cc8-3441ea4220e0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_childMarginal_eq_four_outcomes

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  rw [childMarginal_eq_four_outcomes,
    childMarginal_eq_four_outcomes kernel]
  simp [smoothed]
  ring
end TwoDegenerateGraphs.BinaryPairKernel
