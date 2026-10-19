-- Prove2me | solution 1 for TwoDegenerateGraphs.sampledHammingEdgeEntropyRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/9eed1b0c-b0f1-4374-85fb-fb8a8595b5fd

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_upper_unconditional
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    0 < sampledHammingEdgeEntropyRate := by
  have hwindow := midpointBeta_lt_upper_unconditional
  unfold entropyUpperEndpoint at hwindow
  have hbeta := midpointBeta_lt_one
  have hbits : 0 < 1 - 2 * midpointBeta + binaryEntropy tau := by
    nlinarith
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  unfold sampledHammingEdgeEntropyRate
  rw [hentropy]
  nlinarith [mul_pos hbits log_two_pos]
end TwoDegenerateGraphs
