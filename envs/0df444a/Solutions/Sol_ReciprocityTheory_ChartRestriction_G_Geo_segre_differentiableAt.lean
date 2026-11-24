-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:50.933091+00:00
-- url     : https://prove2.me/submissions/ab68e0e0-d35c-4f63-a1e1-8a808f501524

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB

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
theorem _root_.solution {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => segre (γ y')) y := by
  rw [differentiableAt_pi]
  intro i
  simp only [segre]
  classical
  have key : ∀ s : Finset K, DifferentiableAt ℂ (fun x => ∏ k ∈ s, γ x ⟨k, i k⟩) y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact ((differentiableAt_pi.1 hγ) ⟨a, i a⟩).mul ih
  exact key Finset.univ
end ReciprocityTheory.ChartRestriction.G.Geo
