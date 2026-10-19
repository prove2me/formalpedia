-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.negative_character_invariant_under_lattice_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:26.026804+00:00
-- url     : https://prove2.me/submissions/80766878-9cb8-4b43-809a-c6b7bd889185

import Mathlib
import Definitions.Def_SpherePacking
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


theorem solution (n : Fin d → ℤ)
    (ℓ : (SchwartzMap.referenceIntegerLattice d)) (x : (EuclideanSpace ℝ (Fin d))) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) (x + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) := by
  obtain ⟨m, hm⟩ := SchwartzMap.PoissonSummation.Standard.reference_lattice_element_eq_integer_vector
    (d := d) (ℓ : EuclideanSpace ℝ (Fin d)) ℓ.2
  rw [hm, SchwartzMap.PoissonSummation.Standard.torus_projection_add_integer_vector]

