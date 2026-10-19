-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.negative_character_invariant_under_lattice_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/a92bbc0e-00fd-4107-b493-d92f5342fa82

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
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution (n : Fin d → ℤ)
    (ℓ : (SchwartzMap.referenceIntegerLattice d)) (x : (EuclideanSpace ℝ (Fin d))) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) (x + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) := by
  rcases
      PoissonSummation.Standard.reference_lattice_element_eq_integer_vector (d := d) (x := (ℓ : (EuclideanSpace ℝ (Fin d))))
        ℓ.property with ⟨m, hm⟩
  simp [hm]
end SchwartzMap.PoissonSummation.Standard
