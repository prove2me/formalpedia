-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedCanonicalSpectralOutcome_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/11a5ade6-40a2-4840-b6a9-3e4df27f0550

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalProjectorMatrix_eq

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
    dSVDensityRationalCanonicalPrefixSpectralOutcome
        w N ξ ζ =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        dSVDensityRationalMixedCanonicalRawSource w N ξ ζ := by
  classical
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let T : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let c : ℝ :=
    ‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹
  let K : Matrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    (S : Matrix _ _ ℂ) ⊗ₖ
      (((T⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ))
  unfold dSVDensityRationalCanonicalPrefixSpectralOutcome
    dSVDensityRationalPhysicalAcceptedOutcome
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector]
  unfold dSVDensityRationalMixedCanonicalRawSource
  change
    Matrix.toEuclideanLin K
      (c • toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k *
              dSVDensityRationalPhysicalProjector
                w ζ k).transpose))) =
      c • toLp 2
        (Matrix.vec
          (dSVDensityRationalCanonicalPrefixMask w N ζ *
            dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
            dSVDensityRationalCanonicalPrefixMask w N ξ))
  rw [(Matrix.toEuclideanLin K).map_smul_of_tower]
  congr 1
  apply WithLp.ofLp_injective
  change
    K.mulVec
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k *
              dSVDensityRationalPhysicalProjector
                w ζ k).transpose)) =
      Matrix.vec
        (dSVDensityRationalCanonicalPrefixMask w N ζ *
          dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
          dSVDensityRationalCanonicalPrefixMask w N ξ)
  dsimp [K]
  rw [Matrix.kronecker_mulVec_vec]
  apply congrArg Matrix.vec
  rw [Matrix.blockDiagonal'_mul]
  exact dSVDensityRationalMixedCanonicalProjectorMatrix_eq
    w N ξ ζ
end QuantumParallelRepetition
