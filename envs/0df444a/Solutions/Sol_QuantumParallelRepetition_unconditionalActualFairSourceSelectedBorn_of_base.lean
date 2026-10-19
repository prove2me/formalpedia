-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceSelectedBorn_of_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/1f556561-e0c2-4100-9aa7-2ee278b0e022

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourcePhaseHarmonicWork_norm
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct

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
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
       Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
    (value : ℝ)
    (base_born :
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          UnconditionalSelectedCopyLocalIndex
            P (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) N m ×
          UnconditionalSelectedCopyLocalIndex
            P (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) N m)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (integratorActualC485SelectedAlicePOVM
            G n S D a₀ P N m x)
          (integratorActualC485SelectedBobPOVM
            G n S D b₀ P N m y) x y))
      (dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
        (unconditionalConjugatePureVector ψ)
        (fun _ _ _ => embezzlementState (N * m))) = value := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let e := physical8SelectedGlobalTargetWorkEquiv P N d m
  let stage := dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
    (unconditionalConjugatePureVector ψ)
    (fun _ _ _ => embezzlementState (N * m))
  let work := unconditionalActualFairSourcePhaseHarmonicWork
    P (N * m)
  have work_unit : ‖work‖ = 1 :=
    unconditionalActualFairSourcePhaseHarmonicWork_norm
      phases (Nat.mul_pos grid harmonic)
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e
            (integratorActualC485SourceAlicePOVM G n S D a₀ x))
          (directDSVActualReindexedRetainedPOVM e
            (integratorActualC485SourceBobPOVM G n S D b₀ y)) x y))
      stage = value
  rw [directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
    G e e
    (integratorActualC485SourceAlicePOVM G n S D a₀ x)
    (integratorActualC485SourceBobPOVM G n S D b₀ y)
    x y stage (unconditionalConjugatePureVector ψ) work
    (unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct ψ)]
  change
    ‖work‖ ^ 2 *
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value
  rw [work_unit, one_pow, one_mul, base_born]
end QuantumParallelRepetition
