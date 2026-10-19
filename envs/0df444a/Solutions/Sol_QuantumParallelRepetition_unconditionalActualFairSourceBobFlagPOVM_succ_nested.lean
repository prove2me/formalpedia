-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceBobFlagPOVM_succ_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/39baeaa1-c29f-411e-a25c-c3d7695f6258

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (b₀ : B) {P N L m : ℕ}
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (j : Fin L) (y : Y) :
    unconditionalActualFairSourceBobFlagPOVM
        G n S D denominator numerator nonempty b₀ P N L m
        flag j.succ y =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv
            P N
            (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) m)
          (unitaryConjugatePOVM
            (conjugateUnitary
              (dSVUniformDensityThresholdLeftBobBasis
                (unconditionalActualFairSourceBobTarget
                  G n S D denominator numerator nonempty flag y)))
            (integratorActualC485SourceBobPOVM
              G n S D b₀ y))) := by
  classical
  have same_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases same_instance
  change
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      b₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ q)) j.succ y = _
  exact
    unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      b₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ q)) j y
end QuantumParallelRepetition
