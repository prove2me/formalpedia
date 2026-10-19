-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.reference_lattice_poisson_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/c9cd6d92-35cc-4b29-a7c5-f7fd545826c5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_torus_descended_periodization_comp_projection
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_character_projection_exponential
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_coefficient_torus_periodization
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_summable_fourier_coefficients_torus_periodization

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform
open MeasureTheory
open SchwartzMap SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution (v : (EuclideanSpace ℝ (Fin d))) :
    (∑' ℓ : (SchwartzMap.referenceIntegerLattice d), f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ]) := by
  simpa [torus_descended_periodization_comp_projection (d := d) (f := f) v, lattice_periodized_map_apply (d := d) (f := f), smul_eq_mul,
    fourier_coefficient_torus_periodization (d := d) (f := f), fourier_character_projection_exponential (d := d), mul_assoc,
    mul_left_comm, mul_comm] using!
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := torusDescendedPeriodization (d := d) f)
        (summable_fourier_coefficients_torus_periodization (d := d) (f := f))
        (euclideanTorusProjection (d := d) v)).tsum_eq.symm
end SchwartzMap.PoissonSummation.Standard
