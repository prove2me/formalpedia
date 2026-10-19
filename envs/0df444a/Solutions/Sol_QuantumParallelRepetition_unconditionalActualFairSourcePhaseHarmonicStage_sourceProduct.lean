-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/e2414b6c-061c-4b72-949b-87a63f4dc0ee

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
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {P N d m : ℕ}
    (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (physical8SelectedGlobalTargetWorkEquiv P N d m))
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
          (unconditionalConjugatePureVector ψ)
          (fun _ _ _ => embezzlementState (N * m))) =
      unconditionalMatchedVerifierTensor
        (unconditionalConjugatePureVector ψ)
        (unconditionalActualFairSourcePhaseHarmonicWork
          P (N * m)) := by
  classical
  ext ⟨⟨i, j⟩, ⟨⟨p, a⟩, ⟨q, b⟩⟩⟩
  simp [LinearIsometryEquiv.piLpCongrLeft_apply,
    directDSVActualBilateralRetainedIndexEquiv,
    physical8SelectedGlobalTargetWorkEquiv,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory,
    unconditionalMatchedVerifierTensor,
    unconditionalActualFairSourcePhaseHarmonicWork,
    mul_assoc, mul_left_comm, mul_comm]
end QuantumParallelRepetition
