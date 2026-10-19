-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPhaseCanonical_sourceScale_absorbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/c6e639a7-9d2c-4857-a09d-2b89bbf29e53

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranch_tensor_smul
import Theorems.Thm_QuantumParallelRepetition_unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedTensor_real_smul_work

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
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    {T : Type*} [Fintype T]
    (work : EuclideanSpace ℂ T) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
            w N gamma‖ / Real.sqrt (w * (d : ℝ))) • work) =
      unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedTarget
              w N gamma))
          (fun _ _ _ => embezzlementState m))
        work := by
  let scale : ℝ := Real.sqrt (w * (d : ℝ))
  let mass : ℝ :=
    ‖dSVDensityRationalCanonicalAcceptedTarget w N gamma‖
  let stage :=
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
      B
      (unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val)
      (fun _ _ _ => embezzlementState m)
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have scale_positive : 0 < scale := by
    dsimp [scale]
    positivity
  have scalar : scale * (mass / scale) = mass := by
    field_simp [ne_of_gt scale_positive]
  have factor :=
    unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
      (B := B) (m := m) width grid fine gamma
  change
    scale •
        unconditionalMatchedVerifierTensor
          stage ((mass / scale) • work) = _
  calc
    scale •
        unconditionalMatchedVerifierTensor
          stage ((mass / scale) • work) =
        unconditionalMatchedVerifierTensor
          stage (scale • ((mass / scale) • work)) :=
      unconditionalMatchedTensor_real_smul_work
        scale stage ((mass / scale) • work)
    _ = unconditionalMatchedVerifierTensor
          stage (mass • work) := by
      rw [smul_smul, scalar]
    _ = mass •
          unconditionalMatchedVerifierTensor stage work :=
      (unconditionalMatchedTensor_real_smul_work
        mass stage work).symm
    _ = unconditionalMatchedVerifierTensor
          (mass • stage) work :=
      unconditionalMixedConjugateSelectedBranch_tensor_smul
        mass stage work
    _ = _ := by
      rw [factor]
end QuantumParallelRepetition
