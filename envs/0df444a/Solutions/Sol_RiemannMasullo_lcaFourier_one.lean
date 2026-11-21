-- Prove2me | solution 1 for RiemannMasullo.lcaFourier_one
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:54:48.842088+00:00
-- url     : https://prove2.me/submissions/7c6d2f48-b588-4ecc-9705-537e4d8f3f7b

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L71-L72
import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

theorem solution (f : G → ℂ) (hf : Integrable f μ) :
    lcaFourier μ f 1 = ∫ x, f x ∂μ := by
  simp [lcaFourier]
