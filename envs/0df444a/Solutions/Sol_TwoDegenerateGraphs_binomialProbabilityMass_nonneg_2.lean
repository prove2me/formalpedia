-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialProbabilityMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/31c91fa3-6d26-48b7-8388-1c945d340b01

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount successCount : ℕ) (probability : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity
end TwoDegenerateGraphs
