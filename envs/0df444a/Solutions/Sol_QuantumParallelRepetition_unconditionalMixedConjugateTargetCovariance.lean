-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMixedConjugateTargetCovariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/c941aa42-66d1-428d-83fa-a8deaa0e4427

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPublicBucketPhysicalCoherentTarget_apply
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateCanonicalAcceptedTarget_sum
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSigmaLocalAction_apply

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
    {d N B n : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMixedConjugateSigmaLocalAction
        (m := N * n) B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ) =
    unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (B := B) w n ξ := by
  classical
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (Real.sqrt (w * (d : ℝ)) : ℂ) *
      unconditionalMixedConjugateSigmaLocalAction B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ)
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        star (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (i, j))) *
        embezzlementState (N * n) (a, b)
  rw [unconditionalMixedConjugateSigmaLocalAction_apply]
  simp_rw [conjugateUnitary_apply,
    unconditionalPublicBucketPhysicalCoherentTarget_apply]
  rw [← unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    width grid dimension ξ ζ i j]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring
end QuantumParallelRepetition
