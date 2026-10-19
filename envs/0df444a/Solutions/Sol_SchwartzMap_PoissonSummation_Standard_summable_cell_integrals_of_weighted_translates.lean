-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.summable_cell_integrals_of_weighted_translates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/7fbe1e2c-4556-48c5-8364-bae55d065f41

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_measurable
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_volume_finite
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_weighted_translate_norm_bound

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
theorem _root_.solution (n : Fin d → ℤ) :
    Summable
        (fun ℓ : (SchwartzMap.referenceIntegerLattice d) =>
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
                f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
  let s : Set (EuclideanSpace ℝ (Fin d)) := SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict s
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, s] using! (half_open_unit_cell_volume_finite (d := d))
  have hsum_norm :
      Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) =>
        μ.real Set.univ * ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using!
      (summable_restricted_lattice_translate_norms (d := d) f (ball (d := d))).mul_left (μ.real Set.univ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hsum_norm
  have hle_ae :
      (fun x : (EuclideanSpace ℝ (Fin d)) =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
              f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖) ≤ᵐ[μ] fun _ : (EuclideanSpace ℝ (Fin d)) =>
        ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := by
    refine ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d)) ?_
    intro x hx
    exact fourier_weighted_translate_norm_bound (d := d) (f := f) n ℓ x hx
  have hnonneg :
      (0 : (EuclideanSpace ℝ (Fin d)) → ℝ) ≤ᵐ[μ] fun x : (EuclideanSpace ℝ (Fin d)) =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
              f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ :=
    ae_of_all _ (fun _ => by positivity)
  have hle' :
      (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
              f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂μ) ≤
        μ.real Set.univ * ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := by
    have hle :
        (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
                f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂μ) ≤
          ∫ x, ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ ∂μ :=
      integral_mono_of_nonneg hnonneg
        (integrable_const ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖) hle_ae
    simpa [MeasureTheory.integral_const (μ := μ), smul_eq_mul, mul_comm] using! hle
  simpa [μ, s, mul_comm, mul_left_comm, mul_assoc] using! hle'
end SchwartzMap.PoissonSummation.Standard
