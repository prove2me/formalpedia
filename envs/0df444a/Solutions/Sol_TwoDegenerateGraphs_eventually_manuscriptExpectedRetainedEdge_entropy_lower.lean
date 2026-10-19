-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_manuscriptExpectedRetainedEdge_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/2e341733-6776-4fb8-92fc-6c107b5950f2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_sq_mul_wordCount_eq_exp
import Theorems.Thm_TwoDegenerateGraphs_hammingBall_card
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeCount_eq
import Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingBall_card_entropy_lower
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptHammingRadius_binEntropy_ge

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) := by
  filter_upwards
    [eventually_manuscriptHammingRadius_binEntropy_ge loss hloss]
    with dimension hentropy
  have hdegree :
      Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := manuscriptHammingBall_card_entropy_lower dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp
        ((dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - loss)) /
        ((dimension + 1 : ℕ) : ℝ) =
      (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) * (Real.binEntropy tau - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [hammingRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold sampledHammingEdgeEntropyRate
        ring_nf
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        gcongr
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
        gcongr
    _ = hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) := by
      rw [hammingExpectedRetainedEdgeCount_eq]
end TwoDegenerateGraphs
