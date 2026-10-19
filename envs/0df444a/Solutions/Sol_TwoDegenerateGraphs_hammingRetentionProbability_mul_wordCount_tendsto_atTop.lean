-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionProbability_mul_wordCount_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/77ef3941-e745-4f3c-88a5-4a5107b3fffc

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_one
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_eq_exp

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto
      (fun dimension : ℕ =>
        hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by
  have hrate : 0 < (1 - midpointBeta) * Real.log 2 :=
    mul_pos (sub_pos.mpr midpointBeta_lt_one) log_two_pos
  have hlinear :
      Tendsto
        (fun dimension : ℕ =>
          ((1 - midpointBeta) * Real.log 2) * (dimension : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexponential := Real.tendsto_exp_atTop.comp hlinear
  apply hexponential.congr'
  filter_upwards [] with dimension
  simp only [Function.comp_apply]
  rw [hammingRetentionProbability_mul_wordCount_eq_exp]
  congr 1
  ring
end TwoDegenerateGraphs
