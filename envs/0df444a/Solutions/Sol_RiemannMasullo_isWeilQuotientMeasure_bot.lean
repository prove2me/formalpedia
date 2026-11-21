-- Prove2me | solution 1 for RiemannMasullo.isWeilQuotientMeasure_bot
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:19:06.583217+00:00
-- url     : https://prove2.me/submissions/67410616-8bef-4acb-88da-d56035b9d8a6

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L175-L177
import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _
theorem solution (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    IsWeilQuotientMeasure (⊥ : Subgroup G) μ Measure.count
      (μ.map (QuotientGroup.mk : G → G ⧸ (⊥ : Subgroup G))) := by
  classical
  let B : Subgroup G := ⊥
  letI : BorelSpace (G ⧸ B) := ⟨rfl⟩
  let e : G ≃ₜ* G ⧸ B :=
    { (QuotientGroup.quotientBot (G := G)).symm with
      continuous_toFun := QuotientGroup.continuous_mk
      continuous_invFun := by
        apply QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
        exact continuous_id }
  change IsWeilQuotientMeasure B μ Measure.count (μ.map e)
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf
  have he : MeasurableEmbedding (e : G → G ⧸ B) := e.toHomeomorph.measurableEmbedding
  refine Eq.trans ?_ (he.integral_map (μ := μ) (lcaCosetIntegral B Measure.count f)).symm
  apply integral_congr_ae
  filter_upwards with x
  change f x = lcaCosetIntegral (⊥ : Subgroup G) Measure.count f (QuotientGroup.mk x)
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul (⊥ : Subgroup G) x
  have ha1 : (a : G) = 1 := a.property
  unfold lcaCosetIntegral
  rw [ha, ha1, mul_one, integral_count]
  have hdefault : ((default : (⊥ : Subgroup G)) : G) = 1 :=
    (default : (⊥ : Subgroup G)).property
  simp [hdefault]
