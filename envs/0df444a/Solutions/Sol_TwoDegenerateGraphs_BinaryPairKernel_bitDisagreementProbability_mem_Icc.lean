-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.bitDisagreementProbability_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/46684dc2-50bd-4897-af80-8c683d3d07e8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (parent : Bool)
    (childProbability : ℝ)
    (hzero : 0 ≤ childProbability) (hone : childProbability ≤ 1) :
    0 ≤ bitDisagreementProbability parent childProbability ∧
      bitDisagreementProbability parent childProbability ≤ 1 := by
  cases parent <;> simp [bitDisagreementProbability] <;> constructor <;>
    linarith
end TwoDegenerateGraphs.BinaryPairKernel
