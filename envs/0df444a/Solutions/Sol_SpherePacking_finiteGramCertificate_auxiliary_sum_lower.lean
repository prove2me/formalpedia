-- Prove2me | solution 1 for SpherePacking.finiteGramCertificate_auxiliary_sum_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/4e0db575-531b-4307-a219-efc1b4105874

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteGramCertificate_shift_sum_nonnegative

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {n k L : ℕ} {s : ℝ}
    (certificate : FiniteGramCertificate n k L)
    (C : SphericalCode n s) :
    (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) ≤
      ∑ x ∈ C.points, ∑ y ∈ C.points,
        auxiliaryFiniteGramKernel certificate s x y := by
  have hshift := finiteGramCertificate_shift_sum_nonnegative
    certificate C
  calc
    (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) ≤
      (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) +
      (∑ x ∈ C.points, ∑ y ∈ C.points,
        (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
          isometricPackingKernel certificate.fibre x y) :=
        le_add_of_nonneg_right hshift
    _ = ∑ x ∈ C.points, ∑ y ∈ C.points,
        auxiliaryFiniteGramKernel certificate s x y := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      unfold auxiliaryFiniteGramKernel
      ring
end SpherePacking
