-- Prove2me | solution 1 for RiemannMasullo.lcaCosetIntegral_mk
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:13:14.68411+00:00
-- url     : https://prove2.me/submissions/d6e71717-2118-4097-8315-3f2291dbfa1b

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L161-L164
import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _
theorem solution (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G)
    (hf : Integrable (fun h : H ↦ f (x * (h : G))) μH) :
    lcaCosetIntegral H μH f (QuotientGroup.mk x) =
      ∫ h : H, f (x * (h : G)) ∂μH := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul H x
  unfold lcaCosetIntegral
  rw [ha]
  simpa only [Subgroup.coe_mul, mul_assoc] using
    (integral_mul_left_eq_self (μ := μH) (fun h : H ↦ f (x * (h : G))) a)
