-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPhysicalAcceptedCoherentStage_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/eac75cd3-50bf-43ef-91f4-5071fc02cf8b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_apply
import Theorems.Thm_QuantumParallelRepetition_unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma

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
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ
        (⟨(φ, i), finProdFinEquiv (k, a)⟩,
          ⟨(ψ, j), finProdFinEquiv (l, b)⟩) =
      ePRState B (φ, ψ) *
        dSVDensityRationalCanonicalPrefixSpectralOutcome
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) *
        embezzlementState m (a, b) := by
  rw [unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma,
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_apply
      width grid]
  ring
end QuantumParallelRepetition
