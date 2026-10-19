-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalStoppedPhaseHarmonicDistance_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/7b4eb2d7-4092-4096-8e1f-627e47d607d2

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierTensor_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierTensor_sub_right
import Theorems.Thm_QuantumParallelRepetition_unconditionalStoppedPhaseHarmonic_distance_sq

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
    {J K : Type*} [Fintype K]
    {d B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : J → EuclideanSpace ℂ (Fin d × Fin d))
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1)
    (j : J) :
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (x j) (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (y j) (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      ‖x j - y j‖ ^ 2 := by
  classical
  let sx := dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    B (x j) (fun _ _ _ => embezzlementState m)
  let sy := dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    B (y j) (fun _ _ _ => embezzlementState m)
  have stage : ‖sx - sy‖ ^ 2 = ‖x j - y j‖ ^ 2 :=
    unconditionalStoppedPhaseHarmonic_distance_sq
      phases harmonic (x j) (y j)
  change
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor sx (work (j, k)) -
        unconditionalMatchedVerifierTensor sy
          (work (j, k))‖ ^ 2) ≤ _
  calc
    _ = ∑ k : K, ‖sx - sy‖ ^ 2 * ‖work (j, k)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [unconditionalMatchedVerifierTensor_sub_right,
        unconditionalMatchedVerifierTensor_norm_sq]
    _ = ‖sx - sy‖ ^ 2 *
        (∑ k : K, ‖work (j, k)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ‖sx - sy‖ ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg _) (work_row j)
    _ = _ := stage
end QuantumParallelRepetition
