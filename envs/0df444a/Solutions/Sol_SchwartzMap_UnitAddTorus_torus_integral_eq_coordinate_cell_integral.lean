-- Prove2me | solution 1 for SchwartzMap.UnitAddTorus.torus_integral_eq_coordinate_cell_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/b85b1487-c53a-4066-b662-0adfc2eba801

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_UnitAddTorus_coordinate_torus_projection_measure_preserving
import Theorems.Thm_SchwartzMap_UnitAddTorus_restricted_product_volume_eq_product_restriction

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus
namespace SchwartzMap.UnitAddTorus
theorem _root_.solution (n : ℕ) (t : ℝ) (g : UnitAddTorus (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coordinateTorusProjection n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp := coordinate_torus_projection_measure_preserving n t
  have h1 :
      (∫ y : UnitAddTorus (Fin n), g y) =
        ∫ x, g (coordinateTorusProjection n x) ∂(Measure.pi fun _ : Fin n =>
          (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) := by
    rw [← hmp.map_eq]
    simpa using! (MeasureTheory.integral_map (hφ := hmp.aemeasurable) (f := g)
      (hfm := by simpa [hmp.map_eq] using! hg))
  simpa [(restricted_product_volume_eq_product_restriction n t).symm] using! h1
end SchwartzMap.UnitAddTorus
