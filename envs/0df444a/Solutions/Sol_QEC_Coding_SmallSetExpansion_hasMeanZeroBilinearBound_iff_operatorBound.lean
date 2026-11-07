-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.hasMeanZeroBilinearBound_iff_operatorBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:18.906423+00:00
-- url     : https://prove2.me/submissions/5e500937-4dde-4781-b204-fc8ee199f106

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroOperatorBound_toBilinearBound
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_weightedNeighborSum_eq_degree_mul_sum
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V]
    {M : WeightedGraph V} {degree : Nat} {spectral : ℝ}
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (hSpectralNonnegative : 0 ≤ spectral) :
    HasMeanZeroBilinearBound M spectral ↔
      HasMeanZeroOperatorBound M spectral := by
  constructor
  · intro hBilinear g hg
    let Ag := weightedNeighborSum M g
    have hAg : (∑ v, Ag v) = 0 := by
      dsimp [Ag]
      rw [sum_weightedNeighborSum_eq_degree_mul_sum
        M degree hSymmetric hRegular g, hg, mul_zero]
    have hBound := hBilinear Ag g hAg hg
    have hNormA : 0 ≤ ∑ v, (Ag v) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hNormG : 0 ≤ ∑ v, (g v) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hPairing : adjacencyPairing M Ag g = ∑ v, (Ag v) ^ 2 := by
      unfold adjacencyPairing
      change (∑ v, Ag v * Ag v) = ∑ v, (Ag v) ^ 2
      simp only [pow_two]
    rw [hPairing, abs_of_nonneg hNormA] at hBound
    by_cases hZero : ∑ v, (Ag v) ^ 2 = 0
    · rw [hZero]
      positivity
    · have hPositive : 0 < ∑ v, (Ag v) ^ 2 :=
        lt_of_le_of_ne hNormA (Ne.symm hZero)
      have hSquareRootPositive :
          0 < Real.sqrt (∑ v, (Ag v) ^ 2) := Real.sqrt_pos.2 hPositive
      have hRootProduct :
          Real.sqrt
              ((∑ v, (Ag v) ^ 2) * ∑ v, (g v) ^ 2) =
            Real.sqrt (∑ v, (Ag v) ^ 2) *
              Real.sqrt (∑ v, (g v) ^ 2) := by
        rw [Real.sqrt_mul hNormA]
      rw [hRootProduct] at hBound
      have hCancel :
          Real.sqrt (∑ v, (Ag v) ^ 2) ≤
            spectral * Real.sqrt (∑ v, (g v) ^ 2) := by
        nlinarith [Real.sq_sqrt hNormA]
      nlinarith [Real.sq_sqrt hNormA, Real.sq_sqrt hNormG]
  · exact HasMeanZeroOperatorBound.toBilinearBound hSpectralNonnegative
end QEC.Coding.SmallSetExpansion
