-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_manuscriptVertexCount_power_le_expectedRetainedEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/77e09d86-7c37-4db9-bf23-bda0461f62a7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_eq_exp
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptExpectedRetainedEdge_entropy_lower
import Theorems.Thm_TwoDegenerateGraphs_manuscriptExtremalPower_pos
import Theorems.Thm_TwoDegenerateGraphs_manuscriptEntropyGap_pos
import Theorems.Thm_TwoDegenerateGraphs_sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptVertexCount_le_four_wordMean
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptEntropyGap_dominates_power_constant

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ^
          manuscriptExtremalPower ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
  have hlower :=
    eventually_manuscriptExpectedRetainedEdge_entropy_lower
      manuscriptEntropyGap manuscriptEntropyGap_pos
  have hvertex :=
    eventually_manuscriptVertexCount_le_four_wordMean
  have hconstant :=
    eventually_manuscriptEntropyGap_dominates_power_constant
  filter_upwards [hlower, hvertex, hconstant] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hconstant_half :
      (4 : ℝ) ^ manuscriptExtremalPower ≤
        (Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
    linarith
  have hexponent :
      ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower +
          manuscriptEntropyGap * (dimension : ℝ) =
        (dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - manuscriptEntropyGap) := by
    rw [sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower]
    ring
  calc
    (manuscriptVertexCount dimension : ℝ) ^
        manuscriptExtremalPower ≤
      (4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^
          manuscriptExtremalPower := by
        apply Real.rpow_le_rpow
        · positivity
        · exact hvertex_bound
        · exact manuscriptExtremalPower_pos.le
    _ = (4 : ℝ) ^ manuscriptExtremalPower *
        Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) := by
      rw [hammingRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le,
        ← Real.exp_mul]
    _ ≤ Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) *
        ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      calc
        (4 : ℝ) ^ manuscriptExtremalPower *
            Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) =
          Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            (4 : ℝ) ^ manuscriptExtremalPower := by ring
        _ ≤ Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
              ((dimension + 1 : ℕ) : ℝ)) / 2) :=
          mul_le_mul_of_nonneg_left hconstant_half
            (Real.exp_pos _).le
    _ = (Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
              manuscriptExtremalPower +
            manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]
      ring
    _ = (Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - manuscriptEntropyGap)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [hexponent]
    _ ≤ hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
      gcongr
end TwoDegenerateGraphs
