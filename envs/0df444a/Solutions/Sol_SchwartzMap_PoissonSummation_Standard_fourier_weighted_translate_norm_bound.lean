-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.fourier_weighted_translate_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/e9c327a1-1269-4d90-9f55-a0757ef8d77a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_subset_closed_ball

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
theorem _root_.solution (n : Fin d → ℤ) (ℓ : (SchwartzMap.referenceIntegerLattice d))
    (x : (EuclideanSpace ℝ (Fin d))) (hx : x ∈ SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) :
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
          f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := by
  have hxK : x ∈ (ball (d := d) : Set (EuclideanSpace ℝ (Fin d))) := (half_open_unit_cell_subset_closed_ball (d := d)) hx
  have hmFourier :
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)‖ ≤ 1 := by
    simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using!
      (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
        (PoissonSummation.Standard.euclideanTorusProjection (d := d) x))
  have hsup :
      ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := by
    simpa [translate_apply, ContinuousMap.restrict_apply] using!
      (ContinuousMap.norm_coe_le_norm ((latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))) ⟨x, hxK⟩)
  calc
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
          f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖
        = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)‖ *
            ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp
    _ ≤ 1 * ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by gcongr
    _ = ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp
    _ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := hsup
end SchwartzMap.PoissonSummation.Standard
