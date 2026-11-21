-- Prove2me | solution 1 for RiemannMasullo.weilFundamentalDomain_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:22:13.356644+00:00
-- url     : https://prove2.me/submissions/288c7c8b-5454-4682-92d8-783f6b49a61c

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L217-L219
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
include hH hΔ hbij
theorem solution {f : G → ℂ} (hf : Integrable f μ) :
    HasSum (fun h : H ↦ ∫ x in (fun y : G ↦ y * (h : G)) '' Δ, f x ∂μ)
      (∫ x, f x ∂μ) := by
  classical
  haveI : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let S (h : H) := (fun y : G ↦ y * (h : G)) '' Δ
  have hm (h : H) : MeasurableSet (S h) :=
    (Homeomorph.mulRight (h : G)).measurableEmbedding.measurableSet_image.mpr hΔ
  have hu : (⋃ h : H, S h) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := hbij.2 (QuotientGroup.mk x)
    have hmem : (y : G)⁻¹ * x ∈ H := QuotientGroup.eq.mp hy
    exact Set.mem_iUnion.mpr ⟨⟨_, hmem⟩, y, y.property, by simp⟩
  have hd : Pairwise (fun a b ↦ Disjoint (S a) (S b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hq := congrArg (QuotientGroup.mk' H) he
    have qa : (QuotientGroup.mk' H) (a : G) = 1 := (QuotientGroup.eq_one_iff _).2 a.property
    have qb : (QuotientGroup.mk' H) (b : G) = 1 := (QuotientGroup.eq_one_iff _).2 b.property
    have hxy : (⟨y, hy⟩ : Δ) = ⟨x, hx⟩ := hbij.1 (by
      simpa only [map_mul, qa, qb, mul_one, QuotientGroup.mk'_apply] using hq)
    have heq : y = x := congrArg Subtype.val hxy
    subst y
    exact hab (Subtype.ext (mul_left_cancel he).symm)
  simpa only [hu, Measure.restrict_univ] using
    (hasSum_integral_iUnion hm hd (hf.integrableOn (s := ⋃ h : H, S h)))
