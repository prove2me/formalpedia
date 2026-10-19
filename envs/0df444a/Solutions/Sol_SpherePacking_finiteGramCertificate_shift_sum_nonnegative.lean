-- Prove2me | solution 1 for SpherePacking.finiteGramCertificate_shift_sum_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/cf4dcb65-86da-4f20-a38f-8f493447aad9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteHilbertSchmidtKernel_positive
import Theorems.Thm_SpherePacking_finiteGramCertificate_shift_identity

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
    0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
      (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
        isometricPackingKernel certificate.fibre x y := by
  have hboundary :
      0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.boundary x y := by
    simpa using
      finiteHilbertSchmidtKernel_positive (certificateFibreBasis n k)
        certificate.boundary C.points (fun _ => (1 : ℝ))
  have hremainder :
      0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.remainder x y := by
    simpa using
      finiteHilbertSchmidtKernel_positive (certificateFibreBasis n k)
        certificate.remainder C.points (fun _ => (1 : ℝ))
  calc
    0 ≤
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          finiteHilbertSchmidtKernel (certificateFibreBasis n k)
            certificate.boundary x y) +
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          finiteHilbertSchmidtKernel (certificateFibreBasis n k)
            certificate.remainder x y) :=
      add_nonneg hboundary hremainder
    _ = ∑ x ∈ C.points, ∑ y ∈ C.points,
        (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
          isometricPackingKernel certificate.fibre x y := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      symm
      exact finiteGramCertificate_shift_identity certificate
        (C.unit_norm x hx) (C.unit_norm y hy)
end SpherePacking
