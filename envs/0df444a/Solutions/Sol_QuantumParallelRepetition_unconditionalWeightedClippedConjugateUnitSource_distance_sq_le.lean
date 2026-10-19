-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/79bf2e71-9e78-4aee-b176-15e37a8aff19

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalClippedConjugateUnitTarget_distance_sq_le

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
    {J : Type*} [Fintype J]
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j, weight j) = 1)
    (gamma : J → BipartiteUnitVector d)
    (psi : J → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : ℝ)
    (energy_bound :
      (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) ≤ energy) :
    (∑ j, weight j *
      ‖unconditionalConjugatePureVector (psi j) -
        unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine (gamma j)).val‖ ^ 2) ≤
      2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  classical
  let clip : ℝ := 1 / w + (d : ℝ) * w / (N : ℝ)
  calc
    _ ≤ ∑ j, weight j *
        (2 * ‖psi j - (gamma j).val‖ ^ 2 + 8 * clip) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (unconditionalClippedConjugateUnitTarget_distance_sq_le
          width grid fine (gamma j) (psi j))
        (weight_nonnegative j)
    _ = 2 * (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) +
        (8 * clip) * (∑ j, weight j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 2 * (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) +
        8 * clip := by
      rw [weight_normalized]
      ring
    _ ≤ 2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
      dsimp [clip]
      linarith
end QuantumParallelRepetition
