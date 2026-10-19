-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.torus_integral_eq_euclidean_cell_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/a713cec7-a222-4717-a6a0-7714520bc369

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_UnitAddTorus_torus_integral_eq_coordinate_cell_integral
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_measurable

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators
open MeasureTheory
open SchwartzMap
variable {d : ℕ}
open SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
open UnitAddTorus
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (euclideanTorusProjection (d := d) x) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
        (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) := by
  have h1 :
      (∫ y : UnitAddTorus (Fin d), g y) =
        ∫ x, g (UnitAddTorus.coordinateTorusProjection d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1)) := by
    simpa using!
      (UnitAddTorus.torus_integral_eq_coordinate_cell_integral (n := d) (t := (0 : ℝ)) g hg)
  let f : (Fin d → ℝ) ≃ᵐ (EuclideanSpace ℝ (Fin d)) := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (⇑f) (volume : Measure (Fin d → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    simpa [f, MeasurableEquiv.coe_toLp] using! (PiLp.volume_preserving_toLp (ι := Fin d))
  have hpre :
      f ⁻¹' (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) =
        Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1) := by
    ext x
    simp [f, SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell, MeasurableEquiv.coe_toLp]
  have hmpR :
      MeasurePreserving (⇑f)
        ((volume : Measure (Fin d → ℝ)).restrict
          (f ⁻¹' SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)))
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
          (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d))) :=
    MeasurePreserving.restrict_preimage hmp
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d))
  have h2 :
      (∫ x, g (UnitAddTorus.coordinateTorusProjection d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1))) =
        ∫ y, g (euclideanTorusProjection (d := d) y) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
          (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) := by
    simpa [hpre, euclideanTorusProjection, f] using!
      (MeasurePreserving.integral_comp' hmpR
        (g := fun y : (EuclideanSpace ℝ (Fin d)) => g (UnitAddTorus.coordinateTorusProjection d (WithLp.ofLp y))))
  exact h1.trans h2
end SchwartzMap.PoissonSummation.Standard
