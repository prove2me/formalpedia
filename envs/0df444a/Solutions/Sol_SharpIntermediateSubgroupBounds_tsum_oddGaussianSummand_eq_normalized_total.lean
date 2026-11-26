-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.tsum_oddGaussianSummand_eq_normalized_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:13.534571+00:00
-- url     : https://prove2.me/submissions/17d4d626-df68-40ac-9dff-d5f3aff9b044

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_totalQBinom_odd_split

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, oddGaussianSummand p a j =
      quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
        (totalQBinom p (2 * a + 1) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range (a + 1))]
  · calc
      (∑ j ∈ Finset.range (a + 1), oddGaussianSummand p a j) =
          ∑ j ∈ Finset.range (a + 1),
            2 * quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
              (qBinom p (2 * a + 1) (a + 1 + j) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < a + 1 := Finset.mem_range.mp hj
        have hja : j ≤ a := by omega
        simp [oddGaussianSummand, normalizedOddGaussianRight, hja]
        ring
      _ = 2 * quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
            ∑ j ∈ Finset.range (a + 1),
              (qBinom p (2 * a + 1) (a + 1 + j) : ℝ) := by
        rw [Finset.mul_sum]
      _ = quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
            (totalQBinom p (2 * a + 1) : ℝ) := by
        rw [totalQBinom_odd_split hp]
        push_cast
        ring
  · intro j hj
    have hja : a < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    simp [oddGaussianSummand, normalizedOddGaussianRight, show ¬j ≤ a by omega]
end SharpIntermediateSubgroupBounds
