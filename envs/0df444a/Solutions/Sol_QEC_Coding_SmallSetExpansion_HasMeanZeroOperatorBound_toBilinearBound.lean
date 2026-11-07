-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.HasMeanZeroOperatorBound.toBilinearBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:17:24.301198+00:00
-- url     : https://prove2.me/submissions/1e234c77-29a5-45b8-be09-179290f01bc2

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
section
namespace QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
private theorem abs_sum_mul_le_sqrt_mul_sqrt
    [Fintype V] (f g : V → ℝ) :
    |∑ v, f v * g v| ≤
      Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := by
  calc
    |∑ v, f v * g v| ≤ ∑ v, |f v * g v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v, |f v| * |g v| := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [abs_mul]
    _ ≤ Real.sqrt (∑ v, |f v| ^ 2) *
        Real.sqrt (∑ v, |g v| ^ 2) := by
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := by
      simp_rw [sq_abs]
      rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
end QEC.Coding.SmallSetExpansion
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace HasMeanZeroOperatorBound
theorem _root_.solution
    [Fintype V]
    {M : WeightedGraph V} {spectral : ℝ}
    (hSpectralNonnegative : 0 ≤ spectral)
    (hOperator : HasMeanZeroOperatorBound M spectral) :
    HasMeanZeroBilinearBound M spectral := by
  intro f g _hf hg
  have hCauchy := abs_sum_mul_le_sqrt_mul_sqrt
    f (weightedNeighborSum M g)
  have hOperator' := hOperator g hg
  have hNormF : 0 ≤ ∑ v, (f v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNormG : 0 ≤ ∑ v, (g v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNormA : 0 ≤ ∑ v, (weightedNeighborSum M g v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hProduct :
      (∑ v, (f v) ^ 2) *
          (∑ v, (weightedNeighborSum M g v) ^ 2) ≤
        (∑ v, (f v) ^ 2) *
          (spectral ^ 2 * ∑ v, (g v) ^ 2) :=
    mul_le_mul_of_nonneg_left hOperator' hNormF
  have hRoot := Real.sqrt_le_sqrt hProduct
  calc
    |adjacencyPairing M f g| =
        |∑ v, f v * weightedNeighborSum M g v| := by
      rfl
    _ ≤ Real.sqrt ((∑ v, (f v) ^ 2) *
          ∑ v, (weightedNeighborSum M g v) ^ 2) := hCauchy
    _ ≤ Real.sqrt ((∑ v, (f v) ^ 2) *
          (spectral ^ 2 * ∑ v, (g v) ^ 2)) := hRoot
    _ = spectral *
        Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := by
      rw [show
        (∑ v, (f v) ^ 2) *
              (spectral ^ 2 * ∑ v, (g v) ^ 2) =
            spectral ^ 2 *
              ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg spectral), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hSpectralNonnegative]
end HasMeanZeroOperatorBound
end QEC.Coding.SmallSetExpansion
