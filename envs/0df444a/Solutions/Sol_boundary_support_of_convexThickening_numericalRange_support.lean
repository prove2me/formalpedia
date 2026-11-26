-- Prove2me | solution 1 for boundary_support_of_convexThickening_numericalRange_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:28.404803+00:00
-- url     : https://prove2.me/submissions/e4718547-2fa7-4349-a8c4-03660b1c290c

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
import Theorems.Thm_oriented_carrier_point_of_convexThickening_numericalRange_support
import Theorems.Thm_SmoothJordanDomain_frontier_support_of_support_at_mem_carrier


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0) :
    ∀ (n : ℕ) (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0 := by
  intro n xi hxi t ht
  obtain ⟨w, hwOmega, hwside⟩ :=
    oriented_carrier_point_of_convexThickening_numericalRange_support
      A Omega hcarrier hsupport n
  exact (Omega n).frontier_support_of_support_at_mem_carrier
    w hwOmega t (hwside t) xi hxi
