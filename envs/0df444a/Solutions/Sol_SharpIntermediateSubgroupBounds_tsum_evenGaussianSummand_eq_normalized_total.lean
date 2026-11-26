-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.tsum_evenGaussianSummand_eq_normalized_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:58.614461+00:00
-- url     : https://prove2.me/submissions/09b19996-6470-4a18-8389-f3de16b13c4a

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_totalQBinom_even_split


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenGaussianSummand p a j =
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range (a + 1))]
  · rw [Finset.sum_range_succ']
    have htail : (∑ j ∈ Finset.range a, evenGaussianSummand p a (j + 1)) =
        2 * ((p : ℝ)⁻¹ ^ (a * a) *
          ∑ j ∈ Finset.range a, (qBinom p (2 * a) (a + (j + 1)) : ℝ)) := by
      calc
        (∑ j ∈ Finset.range a, evenGaussianSummand p a (j + 1)) =
            ∑ j ∈ Finset.range a, 2 *
              ((p : ℝ)⁻¹ ^ (a * a) *
                (qBinom p (2 * a) (a + (j + 1)) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < a := Finset.mem_range.mp hj
          have hja : j + 1 ≤ a := by omega
          simp [evenGaussianSummand, centerMultiplicity, normalizedGaussianRight, hja]
        _ = 2 * ((p : ℝ)⁻¹ ^ (a * a) *
              ∑ j ∈ Finset.range a, (qBinom p (2 * a) (a + (j + 1)) : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    rw [htail]
    simp [evenGaussianSummand, centerMultiplicity, normalizedGaussianRight]
    rw [totalQBinom_even_split hp]
    push_cast
    ring
  · intro j hj
    have hja : a < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    simp [evenGaussianSummand, normalizedGaussianRight, show ¬j ≤ a by omega]
end SharpIntermediateSubgroupBounds
