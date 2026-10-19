-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.smoothed_averageDisagreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/73fc3b18-33da-4af3-99b9-2fdbc8983f0b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_averageDisagreement_eq_four_outcomes

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  rw [averageDisagreement_eq_four_outcomes,
    averageDisagreement_eq_four_outcomes kernel]
  simp [smoothed]
  ring
end TwoDegenerateGraphs.BinaryPairKernel
