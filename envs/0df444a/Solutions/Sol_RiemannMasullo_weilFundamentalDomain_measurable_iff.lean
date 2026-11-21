-- Prove2me | solution 1 for RiemannMasullo.weilFundamentalDomain_measurable_iff
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:32:50.903378+00:00
-- url     : https://prove2.me/submissions/8ab1d10b-478d-4bc3-93f9-c444a9cebc4a

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L226-L227
import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _
variable (hH : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable [DiscreteTopology H] [SecondCountableTopology G]
variable {Δ : Set G} (hΔ : MeasurableSet Δ)
variable (hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)))
variable (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ Measure.count ν)
include hH hΔ hbij hν
theorem solution (f : G ⧸ H → ℂ) :
    Measurable f ↔ Measurable (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) := by
  classical
  letI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ H) :=
    QuotientGroup.continuous_mk.measurable
  constructor
  · intro hf
    exact (hf.comp hπ).indicator hΔ
  intro hf
  let q : Δ → G ⧸ H := fun x ↦ QuotientGroup.mk x.val
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  haveI : IsUniformGroup G := isUniformGroup_of_commGroup
  haveI : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity G).IsCountablyGenerated := IsUniformGroup.uniformity_countably_generated
  haveI : PolishSpace G := inferInstance
  haveI : StandardBorelSpace Δ := hΔ.standardBorel
  have hq : MeasurableEmbedding q := (hπ.comp measurable_subtype_coe).measurableEmbedding hbij.1
  have hcomp : Measurable (f ∘ q) := by
    convert (hf.comp (measurable_subtype_coe : Measurable ((↑) : Δ → G))) using 1
    funext x
    exact (Set.indicator_of_mem x.property (fun y : G ↦ f (QuotientGroup.mk y))).symm
  intro s hs
  have heq : q '' (q ⁻¹' (f ⁻¹' s)) = f ⁻¹' s := Set.image_preimage_eq _ hbij.2
  rw [← heq]
  exact hq.measurableSet_image.mpr (hcomp hs)
