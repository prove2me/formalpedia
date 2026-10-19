-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/6f23a646-d506-4c55-a356-805433bf3f0a

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
    {d N B m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin (N * m)) :
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ePRState B (φ, ψ) *
        dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
          w m ξ ζ (⟨i, a⟩, ⟨j, b⟩) := by
  simp [dSVDensityRationalPublicBucketPhysicalCoherentMixedState,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVDensityRationalPublicBucketCoherentPhaseHistory,
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    mul_assoc]
end QuantumParallelRepetition
