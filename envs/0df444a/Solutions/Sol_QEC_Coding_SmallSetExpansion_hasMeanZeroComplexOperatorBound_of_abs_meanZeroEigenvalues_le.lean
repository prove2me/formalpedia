-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.hasMeanZeroComplexOperatorBound_of_abs_meanZeroEigenvalues_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:58.258197+00:00
-- url     : https://prove2.me/submissions/44ffef5e-644e-4cc5-b430-48af1245d76d

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Theorems.Thm_QEC_Coding_SmallSetExpansion_LinearMap_IsSymmetric_norm_sq_apply_le_of_abs_eigenvalues_le
import Theorems.Thm_QEC_Coding_SmallSetExpansion_centeredAdjacencyEuclidean_apply_of_sum_eq_zero
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M)
    {spectral : ℝ} (hSpectralNonnegative : 0 ≤ spectral)
    (hEigen : ∀ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ V)),
      |(centeredAdjacencyEuclidean_isSymmetric M degree hSymmetric).eigenvalues
          rfl i| ≤ spectral) :
    HasMeanZeroComplexOperatorBound M spectral := by
  intro g hg
  let f : EuclideanSpace ℂ V := WithLp.toLp 2 g
  have hBound := LinearMap.IsSymmetric.norm_sq_apply_le_of_abs_eigenvalues_le
    (centeredAdjacencyEuclidean_isSymmetric M degree hSymmetric)
    hSpectralNonnegative hEigen f
  have hCentered : centeredAdjacencyEuclidean M degree f =
      complexAdjacencyEuclidean M f :=
    centeredAdjacencyEuclidean_apply_of_sum_eq_zero M degree f hg
  rw [hCentered] at hBound
  simpa [f, EuclideanSpace.norm_sq_eq] using hBound
end QEC.Coding.SmallSetExpansion
