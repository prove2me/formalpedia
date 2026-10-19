-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.smoothedConditionalEntropy_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/4050a92b-06f7-4259-8490-7d25a1652452

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop
end TwoDegenerateGraphs.BinaryPairKernel
