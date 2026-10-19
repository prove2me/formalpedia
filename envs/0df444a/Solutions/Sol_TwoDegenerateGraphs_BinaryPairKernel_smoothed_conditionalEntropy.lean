-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.smoothed_conditionalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/34ed070b-beea-4c35-8b5b-2cdec8a33a37

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := by
  rfl
end TwoDegenerateGraphs.BinaryPairKernel
