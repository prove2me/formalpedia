-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.fourier_coefficient_torus_periodization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/87f778f0-3ebe-4d72-85f8-a84fbe8968de

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_UnitAddTorus_torus_integral_eq_coordinate_cell_integral
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_measurable
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_cell_is_fundamental_region
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_torus_integral_eq_euclidean_cell_integral
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_torus_descended_periodization_comp_projection
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_negative_fourier_character_projection
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_negative_character_invariant_under_lattice_shift
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_character_translate_integrable_on_cell
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_summable_cell_integrals_of_weighted_translates

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
    UnitAddTorus.mFourierCoeff (torusDescendedPeriodization (d := d) f) n =
      𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) := by
  let χ : (EuclideanSpace ℝ (Fin d)) → ℂ := fun x =>
    UnitAddTorus.mFourier (-n)
      (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)
  let G : (EuclideanSpace ℝ (Fin d)) → ℂ := fun x => χ x * f x
  have hχ_cont : Continuous χ :=
    (UnitAddTorus.mFourier (-n)).continuous.comp
      (PoissonSummation.Standard.continuous_euclidean_torus_projection (d := d))
  have hχ_norm (x : EuclideanSpace ℝ (Fin d)) : ‖χ x‖ ≤ 1 := by
    simpa [χ, UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using!
      (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
        (PoissonSummation.Standard.euclideanTorusProjection (d := d) x))
  have hG_int : Integrable G (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    refine f.integrable.norm.mono' (hχ_cont.mul f.continuous).aestronglyMeasurable ?_
    filter_upwards [] with x
    change ‖χ x * f x‖ ≤ ‖f x‖
    calc
      ‖χ x * f x‖ = ‖χ x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ 1 * ‖f x‖ := by gcongr; exact hχ_norm x
      _ = ‖f x‖ := one_mul _
  have hχ_shift (ℓ : SchwartzMap.referenceIntegerLattice d)
      (x : EuclideanSpace ℝ (Fin d)) : χ (x + (ℓ : EuclideanSpace ℝ (Fin d))) = χ x :=
    negative_character_invariant_under_lattice_shift (d := d) n ℓ x
  have htranslate (ℓ : SchwartzMap.referenceIntegerLattice d) :
      (∫ x in
        (fun y : EuclideanSpace ℝ (Fin d) =>
          (ℓ : EuclideanSpace ℝ (Fin d)) + y) ''
          SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d), G x) =
        ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
          χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
    let s : Set (EuclideanSpace ℝ (Fin d)) :=
      SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)
    let t : Set (EuclideanSpace ℝ (Fin d)) :=
      (fun y : EuclideanSpace ℝ (Fin d) =>
        (ℓ : EuclideanSpace ℝ (Fin d)) + y) '' s
    have hs : MeasurableSet s :=
      SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d)
    have hls : MeasurableSet t := by
      have hpre :
          t = (fun x : EuclideanSpace ℝ (Fin d) =>
            -(ℓ : EuclideanSpace ℝ (Fin d)) + x) ⁻¹' s := by
        ext x
        simp [t]
      rw [hpre]
      exact (continuous_const.add continuous_id).measurable hs
    have hmem (x : EuclideanSpace ℝ (Fin d)) :
        ((ℓ : EuclideanSpace ℝ (Fin d)) + x ∈ t) ↔ x ∈ s := by
      simp [t]
    calc
      (∫ x in t, G x) = ∫ x, t.indicator G x :=
        (integral_indicator hls).symm
      _ = ∫ x, t.indicator G ((ℓ : EuclideanSpace ℝ (Fin d)) + x) :=
        (integral_add_left_eq_self (t.indicator G)
          (ℓ : EuclideanSpace ℝ (Fin d))).symm
      _ = ∫ x, s.indicator
          (fun x : EuclideanSpace ℝ (Fin d) => G ((ℓ : EuclideanSpace ℝ (Fin d)) + x)) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ s
        · simp [hx, (hmem x).2 hx]
        · simp [hx, mt (hmem x).1 hx]
      _ = ∫ x in s, G ((ℓ : EuclideanSpace ℝ (Fin d)) + x) := integral_indicator hs
      _ = ∫ x in s, χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [G, add_comm, hχ_shift]
  have hglobal :
      (∫ x : EuclideanSpace ℝ (Fin d), G x) =
        ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
    rw [(half_open_cell_is_fundamental_region (d := d)).integral_eq_tsum G hG_int]
    apply tsum_congr
    intro ℓ
    change (∫ x in
      (fun y : EuclideanSpace ℝ (Fin d) =>
        (ℓ : EuclideanSpace ℝ (Fin d)) + y) ''
        SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d), G x) = _
    exact htranslate ℓ
  calc
    UnitAddTorus.mFourierCoeff (torusDescendedPeriodization (d := d) f) n =
        ∫ y : UnitAddTorus (Fin d),
          UnitAddTorus.mFourier (-n) y * torusDescendedPeriodization (d := d) f y := by
      rw [UnitAddTorus.mFourierCoeff_eq_integral
        (torusDescendedPeriodization (d := d) f) n (fun _ => 0)]
      have hset :
          {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)} =
            Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1)) := by
        ext x
        simp
      rw [hset]
      simpa [UnitAddTorus.coordinateTorusProjection, smul_eq_mul] using!
        (UnitAddTorus.torus_integral_eq_coordinate_cell_integral (n := d) (t := 0)
          (fun y : UnitAddTorus (Fin d) =>
            UnitAddTorus.mFourier (-n) y * torusDescendedPeriodization (d := d) f y)
          (((UnitAddTorus.mFourier (-n)).continuous.mul
            (torusDescendedPeriodization (d := d) f).continuous).aestronglyMeasurable)).symm
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
          χ x * latticePeriodizedMap (d := d) f x := by
      rw [torus_integral_eq_euclidean_cell_integral
        (fun y : UnitAddTorus (Fin d) =>
          UnitAddTorus.mFourier (-n) y * torusDescendedPeriodization (d := d) f y)
        (((UnitAddTorus.mFourier (-n)).continuous.mul
          (torusDescendedPeriodization (d := d) f).continuous).aestronglyMeasurable)]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [χ, torus_descended_periodization_comp_projection]
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
          ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
            χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [lattice_periodized_map_apply]
      exact tsum_mul_left.symm
    _ = ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
      exact (integral_tsum_of_summable_integral_norm
        (fun ℓ => fourier_character_translate_integrable_on_cell (d := d) f n ℓ)
        (summable_cell_integrals_of_weighted_translates (d := d) f n)).symm
    _ = ∫ x : EuclideanSpace ℝ (Fin d), G x := hglobal.symm
    _ = 𝓕 (fun x : EuclideanSpace ℝ (Fin d) => f x)
          (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [G, χ, negative_fourier_character_projection,
        Real.fourierChar_apply, smul_eq_mul]
      congr 1
      push_cast
      ring_nf
end SchwartzMap.PoissonSummation.Standard
