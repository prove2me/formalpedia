-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedCanonicalRawSource_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/053337c0-d34d-4cb1-b63e-bb39bbb1f9bf

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalPrefixMask_eq_diagonal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (k l : Fin N) (i j : Fin d) :
    dSVDensityRationalMixedCanonicalRawSource
        w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) =
      if k = l ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N l
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true
      then
        dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j
      else 0 := by
  classical
  unfold dSVDensityRationalMixedCanonicalRawSource
  rw [dSVDensityRationalCanonicalPrefixMask_eq_diagonal w N ζ,
    dSVDensityRationalCanonicalPrefixMask_eq_diagonal w N ξ]
  change
    (Matrix.diagonal
        (fun q : DSVUniformDensityThresholdLocalIndex N d =>
          if dSVDensityRationalProjectiveThresholdBin w N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues q.2) = true
          then (1 : ℂ) else 0) *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        Matrix.diagonal
          (fun q : DSVUniformDensityThresholdLocalIndex N d =>
            if dSVDensityRationalProjectiveThresholdBin w N q.1
                ((dSVSoftBobLeftReducedDensity_posSemidef
                  ξ).isHermitian.eigenvalues q.2) = true
            then (1 : ℂ) else 0)) ⟨l, j⟩ ⟨k, i⟩ = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases flags : k = l
  · subst l
    by_cases alice :
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
    · by_cases bob :
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true
      · simp [dSVDensityRationalMixedCanonicalCrossMatrix,
          dSVDensityRationalLocalSpectralPairBasisOverlap,
          Matrix.blockDiagonal'_apply, alice, bob]
      · simp [bob]
    · simp [alice]
  · simp [dSVDensityRationalMixedCanonicalCrossMatrix,
      Matrix.blockDiagonal'_apply, flags]
end QuantumParallelRepetition
