-- Prove2me | solution 1 for RiemannMasullo.lcaConvolution_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:56:19.058653+00:00
-- url     : https://prove2.me/submissions/7900b3a7-bf0a-4c79-98c3-1a5e24c40b5c

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L81-L82
import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

theorem solution [Subsingleton G] (f g : G → ℂ) (x : G) :
    lcaConvolution μ f g x = (μ univ).toReal * f x * g x := by
  unfold lcaConvolution
  have h (y : G) : f y * g (y⁻¹ * x) = f x * g x := by
    rw [Subsingleton.elim y x, Subsingleton.elim (x⁻¹ * x) x]
  simp_rw [h]
  rw [integral_const]
  simp [Measure.real, Complex.real_smul, mul_assoc]
