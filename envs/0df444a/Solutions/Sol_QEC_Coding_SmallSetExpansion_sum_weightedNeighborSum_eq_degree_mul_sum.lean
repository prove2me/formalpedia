-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_weightedNeighborSum_eq_degree_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:17:51.919843+00:00
-- url     : https://prove2.me/submissions/6669fc77-101d-4b22-a3b9-83bba91fe960

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (g : V → ℝ) :
    ∑ v, weightedNeighborSum M g v = degree * ∑ v, g v := by
  classical
  unfold weightedNeighborSum
  rw [Finset.sum_comm]
  calc
    (∑ u, ∑ v, (M v u : ℝ) * g u) =
        ∑ u, g u * ∑ v, (M u v : ℝ) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hSymmetric]
      ring
    _ = ∑ u, g u * degree := by
      apply Finset.sum_congr rfl
      intro u _hu
      congr 1
      exact_mod_cast hRegular u
    _ = degree * ∑ u, g u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
end QEC.Coding.SmallSetExpansion
