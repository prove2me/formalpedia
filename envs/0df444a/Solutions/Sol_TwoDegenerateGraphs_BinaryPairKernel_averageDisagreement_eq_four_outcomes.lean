-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.averageDisagreement_eq_four_outcomes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/82972c4a-d8ab-4a9e-9caf-87f00acf49b9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel) :
    kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        kernel.parentProbability * (1 - kernel.parentProbability) +
        kernel.parentProbability ^ 2 *
          (1 - kernel.childProbability true true) := by
  simp [averageDisagreement, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass,
    bitDisagreementProbability]
  ring
end TwoDegenerateGraphs.BinaryPairKernel
