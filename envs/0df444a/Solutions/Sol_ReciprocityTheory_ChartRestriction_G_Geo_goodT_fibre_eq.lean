-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.goodT_fibre_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:44.51883+00:00
-- url     : https://prove2.me/submissions/136d1389-db66-4ad0-a81f-a8e8434922bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) :
    goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) := by
  ext u
  constructor
  · rintro ⟨hu, hy'⟩
    have hx := (A.chart j).map_target hu.1
    have hxS : (A.chart j).symm u ∉ S := fun hS => hy ⟨u, ⟨hu, hS⟩, hy'⟩
    exact ⟨(A.chart j).symm u, ⟨hx, hy', hxS⟩, (A.chart j).right_inv hu.1⟩
  · rintro ⟨x, ⟨hx, hqx, hxS⟩, rfl⟩
    have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
    obtain ⟨h1, h2⟩ := hq x hxS j hx
    refine ⟨⟨(A.chart j).map_source hx, h1, h2⟩, ?_⟩
    show q ((A.chart j).symm (A.chart j x)) ∈ ({y} : Set (Fin e → ℂ))
    rw [hl]
    exact hqx
end ReciprocityTheory.ChartRestriction.G.Geo
