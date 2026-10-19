-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/8ead470a-3b54-4a84-88bd-09267d130f31

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
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix.blockDiagonal'
        (dSVDensityRationalPhysicalProjector w ξ) =
      (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalCanonicalPrefixMask w N ξ *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal'
      (dSVDensityRationalPhysicalProjector w ξ) =
      Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ)) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            Matrix.diagonal fun i : Fin d =>
              if dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = true
              then (1 : ℂ) else 0) *
        Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
              Matrix.unitaryGroup (Fin d) ℂ) :
                Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext k
  unfold dSVDensityRationalPhysicalProjector
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
  rw [spectralPartitionPOVM_effect_eq_spectralDiagonal]
  rfl
end QuantumParallelRepetition
