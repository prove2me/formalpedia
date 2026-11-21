-- Prove2me | solution 1 for RiemannMasullo.tamagawaFourier_eq_lcaFourier
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:57:37.058878+00:00
-- url     : https://prove2.me/submissions/634684fb-f4e4-4b85-a32d-e0e61dd185f6

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L204-L208
import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
variable {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace R]
local instance : MeasurableSpace (Multiplicative R) := ‹MeasurableSpace R›

theorem solution (μ : Measure R) (ψ : R → Circle) (f : R → ℂ)
    (y : R) (χ : PontryaginDual (Multiplicative R))
    (hχ : ∀ x : R, χ (Multiplicative.ofAdd x) = ψ (x * y)) :
    tamagawaFourier μ ψ f y = lcaFourier (G := Multiplicative R) μ
      (fun x ↦ f x.toAdd) χ := by
  unfold tamagawaFourier lcaFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    congrArg (fun z : Circle ↦ f x * star (z : ℂ)) (hχ x).symm
