-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_balancedHazard_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/52f49252-06dd-4ea2-a82e-febebefb508f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactorBucketCoefficient_nonneg
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_fourthRoot_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {a rho : ℝ}
    (positive : 0 < a)
    (rho_nonnegative : 0 ≤ rho) :
    Real.sqrt
      ((34 / Real.sqrt a) * a + 4 * rho ^ 2 +
        unconditionalPrefactorBucketCoefficient * Real.sqrt a) ≤
      Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
          a ^ (1 / 4 : ℝ) + 2 * rho := by
  have root_positive : 0 < Real.sqrt a := Real.sqrt_pos.2 positive
  have root_square : (Real.sqrt a) ^ 2 = a :=
    Real.sq_sqrt positive.le
  have coefficient_nonnegative :=
    unconditionalPrefactorBucketCoefficient_nonneg
  have coefficient_square :
      (Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient)) ^ 2 =
        34 + unconditionalPrefactorBucketCoefficient :=
    Real.sq_sqrt (by linarith)
  have fourth_square :=
    unconditionalPrefactor_fourthRoot_sq positive.le
  have product_square :
      (Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
        a ^ (1 / 4 : ℝ)) ^ 2 =
        (34 + unconditionalPrefactorBucketCoefficient) *
          Real.sqrt a := by
    calc
      (Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
        a ^ (1 / 4 : ℝ)) ^ 2 =
          (Real.sqrt (34 +
            unconditionalPrefactorBucketCoefficient)) ^ 2 *
            (a ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = (34 + unconditionalPrefactorBucketCoefficient) *
          Real.sqrt a := by rw [coefficient_square, fourth_square]
  have quotient : (34 / Real.sqrt a) * a = 34 * Real.sqrt a := by
    field_simp [ne_of_gt root_positive]
    nlinarith [root_square]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [quotient]
    have cross_nonnegative :
        0 ≤ (Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) *
          a ^ (1 / 4 : ℝ)) * rho :=
      mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (Real.rpow_nonneg positive.le _))
        rho_nonnegative
    nlinarith [product_square]
end QuantumParallelRepetition
