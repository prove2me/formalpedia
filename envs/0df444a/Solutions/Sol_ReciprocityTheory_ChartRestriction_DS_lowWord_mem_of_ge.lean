-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowWord_mem_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:54.868671+00:00
-- url     : https://prove2.me/submissions/de8ccbde-a4cc-4d62-b6a0-af7d1dea8155

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : ∀ a, E a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a) (hε : ε a = ε b) :
    E a b (lowWord E y l) ∈ kLowSpan ε E y := by
  rcases hab.lt_or_eq with h | h
  · exact lowWord_mem (ε := ε) (E := E) (y := y) (l := (a, b) :: l) (by
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]; exact And.intro h hε
      · exact hl p hp)
  · rw [h, lowWord_wt hE hy l a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)
end ReciprocityTheory.ChartRestriction.DS
