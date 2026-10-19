-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.fourier_character_translate_integrable_on_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/d9bbcf4d-ae87-454e-a6e8-11c7bab4bf05

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_measurable
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_subset_closed_ball
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_volume_finite

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
    (ℓ : (SchwartzMap.referenceIntegerLattice d)) :
    IntegrableOn
        (fun x : (EuclideanSpace ℝ (Fin d)) =>
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d)))))
        (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  let K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) :=
    ⟨Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d), isCompact_closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d)⟩
  have hK : SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d) ⊆ (K : Set (EuclideanSpace ℝ (Fin d))) :=
    (half_open_unit_cell_subset_closed_ball (d := d))
  have hbound :
      ∀ x ∈ SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖ := by
    intro x hx
    have hxK : x ∈ (K : Set (EuclideanSpace ℝ (Fin d))) := hK hx
    have hmFourier :
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)‖ ≤ 1 := by
      simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using!
        (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
          (PoissonSummation.Standard.euclideanTorusProjection (d := d) x))
    have hsup :
        ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖ := by
      simpa [translate_apply, ContinuousMap.restrict_apply] using!
        (ContinuousMap.norm_coe_le_norm ((latticeTranslatedMap (d := d) f ℓ).restrict K) ⟨x, hxK⟩)
    calc
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖
          = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)‖ *
              ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp
      _ ≤ 1 * ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by gcongr
      _ = ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp
      _ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖ := hsup
  refine Measure.integrableOn_of_bounded (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (s := SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d))
      (s_finite := (half_open_unit_cell_volume_finite (d := d)).ne)
      ?_
      (M := ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖)
      ?_
  ·
    exact
      (((UnitAddTorus.mFourier (-n)).continuous.comp
            (PoissonSummation.Standard.continuous_euclidean_torus_projection (d := d))).mul
          (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  ·
    exact ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d)) hbound
end SchwartzMap.PoissonSummation.Standard
