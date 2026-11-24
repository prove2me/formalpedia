-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mem_secSet_of_sheet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:00.513928+00:00
-- url     : https://prove2.me/submissions/57e21e5d-88d0-4ec8-9ae8-f37a5237b704

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt

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
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ secSet P Ψ B := by
  refine ⟨fun y hy => Set.indicator_of_notMem hy _, ?_, fun y hy => ?_⟩
  · have hd : DifferentiableOn ℂ (fun y' => segre (γ y')) B := fun y' hy' =>
      (segre_differentiableAt (h y' hy').1).differentiableWithinAt
    exact hd.congr (fun y' hy' => Set.indicator_of_mem hy' _)
  · rw [Set.indicator_of_mem hy]
    exact ⟨γ y, (h y hy).2.1, rfl, (h y hy).2.2⟩
end ReciprocityTheory.ChartRestriction.G.Geo
