-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedCanonicalCrossGauge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/7afbfd28-d657-47f3-8afd-f62f2b50e269

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) =
      dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ := by
  rw [← dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose ζ,
    ← dSVUniformDensityPhysicalSpectralAliceCopy_transpose ξ,
    ← Matrix.transpose_mul]
  unfold dSVDensityRationalMixedCanonicalCrossMatrix
  congr 1
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal' (fun _ : Fin N =>
      (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
        Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) *
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (dSVUniformDensityThresholdLeftBobBasis ζ :
          Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (unitaryBasisOverlap
          (dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvectorUnitary
          (dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvectorUnitary :
          Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul]
  rfl
end QuantumParallelRepetition
