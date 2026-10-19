-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalWeightedStoppedPhaseHarmonicClippedUnit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/3ffc7998-74f3-4b87-b217-8189efdcbee6

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
import Theorems.Thm_QuantumParallelRepetition_unconditionalStoppedPhaseHarmonicDistance_sum_le

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
    {J K : Type*} [Fintype J] [Fintype K]
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (phases : 0 < B) (harmonic : 0 < m)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j, weight j) = 1)
    (gamma : J → BipartiteUnitVector d)
    (psi : J → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : ℝ)
    (energy_bound :
      (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) ≤ energy)
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1) :
    (∑ j : J, weight j * ∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (unconditionalConjugatePureVector (psi j))
            (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B
            (unconditionalConjugatePureVector
              (dSVDensityRationalCanonicalAcceptedUnitTarget
                width grid fine (gamma j)).val)
            (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  classical
  calc
    _ ≤ ∑ j : J, weight j *
        ‖unconditionalConjugatePureVector (psi j) -
          unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine (gamma j)).val‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (unconditionalStoppedPhaseHarmonicDistance_sum_le
          phases harmonic
          (fun i => unconditionalConjugatePureVector (psi i))
          (fun i => unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine (gamma i)).val)
          work work_row j)
        (weight_nonnegative j)
    _ ≤ _ :=
      unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
        width grid fine weight weight_nonnegative weight_normalized
        gamma psi energy energy_bound
end QuantumParallelRepetition
