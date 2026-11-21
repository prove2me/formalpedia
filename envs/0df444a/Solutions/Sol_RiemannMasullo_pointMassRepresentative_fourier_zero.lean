-- Prove2me | solution 1 for RiemannMasullo.pointMassRepresentative_fourier_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:57:36.473066+00:00
-- url     : https://prove2.me/submissions/4cfcf779-04fd-4e92-908a-e63eda81d5e7

-- New supporting theorem for the paper gap noted in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L135-L137
import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
noncomputable local instance : MeasurableSpace (Multiplicative ℝ) := (inferInstance : MeasurableSpace ℝ)

theorem solution (f : ℝ → ℂ) (hf : f = Set.indicator ({0} : Set ℝ) (fun _ ↦ (1 : ℂ))) :
    f 0 = 1 ∧ Integrable f volume ∧
      ∀ χ : PontryaginDual (Multiplicative ℝ),
        lcaFourier (G := Multiplicative ℝ) (show Measure (Multiplicative ℝ) from (volume : Measure ℝ))
          (fun x ↦ f x.toAdd) χ = 0 := by
  subst f
  have h : Set.indicator ({0} : Set ℝ) (fun _ ↦ (1 : ℂ)) =ᵐ[volume] 0 := by
    have he : ∀ᵐ x : ℝ ∂volume, x ∉ ({0} : Set ℝ) := by
      rw [ae_iff]
      simpa using (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))
    filter_upwards [he] with x hx
    exact Set.indicator_of_notMem hx _
  refine ⟨by simp, (integrable_zero _ _ _).congr h.symm, ?_⟩
  intro χ
  unfold lcaFourier
  apply integral_eq_zero_of_ae
  filter_upwards [h] with x hx
  change Set.indicator ({0} : Set ℝ) _ x * _ = 0
  rw [show Set.indicator ({0} : Set ℝ) (fun _ ↦ (1 : ℂ)) x = 0 from hx, zero_mul]
