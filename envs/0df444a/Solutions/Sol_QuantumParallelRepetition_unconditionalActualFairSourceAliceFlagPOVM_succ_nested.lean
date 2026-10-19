-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceAliceFlagPOVM_succ_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/fb1034fd-860a-453d-a234-b99b1617b70e

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
    [decA : DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) {P N L m : ℕ}
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (j : Fin L) (x : X) :
    unconditionalActualFairSourceAliceFlagPOVM
        G n S D denominator numerator nonempty a₀ P N L m
        flag j.succ x =
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
              (dSVDensityRationalCanonicalAliceBasis
                (unconditionalActualFairSourceAliceTarget
                  G n S D denominator numerator nonempty flag x)))
            (integratorActualC485SourceAlicePOVM
              G n S D a₀ x))) := by
  classical
  have same_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  cases same_instance
  change
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      a₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ q)) j.succ x = _
  exact
    unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      a₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ q)) j x
end QuantumParallelRepetition
