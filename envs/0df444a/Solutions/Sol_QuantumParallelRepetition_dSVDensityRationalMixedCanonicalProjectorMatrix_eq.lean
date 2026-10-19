-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedCanonicalProjectorMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/80d44e57-ac06-4b78-b5a6-fb20f4541f86

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalPrefixMask_transpose
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalCrossGauge_eq

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
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ := by
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let X : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ξ
  let Z : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let XI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((X⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let ZI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((Z⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ξ
  let R : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ζ
  have physical_x :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) =
        (((S⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          M * (S : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ξ
  have physical_z :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k) =
        ((((dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          R * (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) ζ : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ζ
  have transpose_x :
      (S : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ξ
  have transpose_z :
      (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ : Matrix
            (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ζ
  have inverse_x :
      (((S⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((X⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ξ
  have inverse_z :
      ((((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((Z⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ζ
  have cancel_x :
      XI * (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp X.property
  have cancel_z :
      ZI * (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp Z.property
  change
    ZI *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (S : Matrix _ _ ℂ).transpose =
        R * dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ * M
  calc
    _ = ((ZI * (Z : Matrix _ _ ℂ)) * R) *
        (ZI * (X : Matrix _ _ ℂ)) *
        (M * (XI * (X : Matrix _ _ ℂ))) := by
          rw [physical_x, physical_z]
          dsimp only [XI, ZI]
          simp only [Matrix.transpose_mul,
            dSVDensityRationalCanonicalPrefixMask_transpose,
            transpose_x, transpose_z, inverse_x, inverse_z,
            Matrix.mul_assoc, M, R]
    _ = R * (ZI * (X : Matrix _ _ ℂ)) * M := by
          rw [cancel_x, cancel_z]
          simp
    _ = _ := by
      dsimp only [ZI]
      rw [dSVDensityRationalMixedCanonicalCrossGauge_eq N ξ ζ]
end QuantumParallelRepetition
