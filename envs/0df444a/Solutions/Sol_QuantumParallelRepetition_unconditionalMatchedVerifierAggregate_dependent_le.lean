-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierAggregate_dependent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/98864f3d-23bb-463f-94ef-d80fa83fbf2d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierAggregate_dependent_continuity

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
    {H : J → Type*}
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℂ (H j)]
    (weight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ weight j)
    (effect : (j : J) → (H j →L[ℂ] H j))
    (contraction : ∀ j, ‖effect j‖ ≤ 1)
    (actual ideal : (j : J) → H j)
    (actual_mass : (∑ j : J, weight j * ‖actual j‖ ^ 2) ≤ 1)
    (ideal_mass : (∑ j : J, weight j * ‖ideal j‖ ^ 2) ≤ 1)
    (Δ : ℝ)
    (deviation :
      (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) ≤ Δ) :
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
      (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      2 * Real.sqrt Δ := by
  have actual_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖actual j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have ideal_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖ideal j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have error_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have actual_root :
      Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) ≤ 1 := by
    nlinarith [
      Real.sq_sqrt actual_nonnegative,
      Real.sqrt_nonneg (∑ j : J, weight j * ‖actual j‖ ^ 2)]
  have ideal_root :
      Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2) ≤ 1 := by
    nlinarith [
      Real.sq_sqrt ideal_nonnegative,
      Real.sqrt_nonneg (∑ j : J, weight j * ‖ideal j‖ ^ 2)]
  calc
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
        (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) :=
          unconditionalMatchedVerifierAggregate_dependent_continuity
            weight nonnegative effect contraction actual ideal
    _ ≤ 2 * Real.sqrt Δ := by
      apply mul_le_mul
      · linarith
      · exact Real.sqrt_le_sqrt deviation
      · exact Real.sqrt_nonneg _
      · norm_num
end QuantumParallelRepetition
