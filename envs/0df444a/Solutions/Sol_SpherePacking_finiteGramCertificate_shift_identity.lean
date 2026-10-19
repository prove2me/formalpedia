-- Prove2me | solution 1 for SpherePacking.finiteGramCertificate_shift_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/736ede9c-a801-439c-910f-8060a7247397

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteHilbertSchmidtKernel_three_channel

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
    {n k L : ℕ} (certificate : FiniteGramCertificate n k L)
    {x y : Euclidean n}
    (hx : x ∈ unitSphere n) (hy : y ∈ unitSphere n) :
    (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
        isometricPackingKernel certificate.fibre x y =
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        certificate.boundary x y +
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        certificate.remainder x y := by
  let S := {z : Euclidean n // z ∈ unitSphere n}
  have hthree := finiteHilbertSchmidtKernel_three_channel
    (certificateFibreBasis n k)
    (fun z : S => certificate.bulk z.val)
    (fun z : S => certificate.boundary z.val)
    (fun z : S => certificate.remainder z.val)
    certificate.spectralCoefficient (1 : ℝ)
    (fun u v i => certificate.bulk_boundary_orthogonal
      u.val u.property v.val v.property i)
    (fun u v i => certificate.bulk_remainder_orthogonal
      u.val u.property v.val v.property i)
    (fun u v i => certificate.boundary_remainder_orthogonal
      u.val u.property v.val v.property i)
    (⟨x, hx⟩ : S) (⟨y, hy⟩ : S)
  have hdecomp :
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        certificate.lift x y =
        certificate.spectralCoefficient ^ 2 *
          finiteHilbertSchmidtKernel (certificateFibreBasis n k)
            certificate.bulk x y +
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.boundary x y +
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.remainder x y := by
    unfold finiteHilbertSchmidtKernel
    rw [certificate.decomposition x hx,
      certificate.decomposition y hy]
    simpa [finiteHilbertSchmidtKernel] using hthree
  rw [certificate.lift_kernel x hx y hy,
    certificate.bulk_kernel x hx y hy,
    certificate.spectralCoefficient_sq] at hdecomp
  linarith
end SpherePacking
