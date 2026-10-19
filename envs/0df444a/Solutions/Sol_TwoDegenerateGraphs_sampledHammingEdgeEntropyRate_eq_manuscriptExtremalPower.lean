-- Prove2me | solution 1 for TwoDegenerateGraphs.sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/4d895ce2-612f-4b85-b91d-e68717083e85

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    sampledHammingEdgeEntropyRate =
      (1 - midpointBeta) * manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
  have hmidpoint :
      entropyUpperEndpoint - midpointBeta =
        certifiedWindowWidth / 2 := by
    have hwindow := entropyWindow_eq_certifiedWindowWidth
    unfold midpointBeta
    linarith
  have hupper :
      binaryEntropy tau = (entropyUpperEndpoint + 1) / 2 := by
    unfold entropyUpperEndpoint
    ring
  have hgain :
      (1 - midpointBeta) * exponentGain =
        certifiedWindowWidth / 8 := by
    have hnonzero : 1 - midpointBeta ≠ 0 :=
      (sub_pos.mpr midpointBeta_lt_one).ne'
    unfold exponentGain
    field_simp [hnonzero]
  have hbits :
      1 - 2 * midpointBeta + binaryEntropy tau =
        (1 - midpointBeta) *
            ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8 := by
    nlinarith [hmidpoint, hupper, hgain]
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  calc
    sampledHammingEdgeEntropyRate =
        (1 - 2 * midpointBeta + binaryEntropy tau) *
          Real.log 2 := by
      unfold sampledHammingEdgeEntropyRate
      rw [hentropy]
      ring
    _ = ((1 - midpointBeta) *
          ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8) * Real.log 2 := by
      rw [hbits]
    _ = (1 - midpointBeta) *
          manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
      unfold manuscriptExtremalPower manuscriptEntropyGap
      ring
end TwoDegenerateGraphs
