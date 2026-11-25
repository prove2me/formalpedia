-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.khw_line_of_kIrrHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:56.308423+00:00
-- url     : https://prove2.me/submissions/b6a002bc-3b59-4af5-bc58-b1d40ce08f1f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_self_mem_kLowSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_line

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : IsKIrrHW ε E μ S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxw : IsKHWVec ε E μ x)
    (hyw : IsKHWVec ε E μ y) (hy0 : y ≠ 0) : ∃ c : ℂ, x = c • y := by
  have hS' : FiniteDimensional ℂ S ∧ IsKStableSub ε E S ∧
      (∀ S' : Submodule ℂ M, S' ≤ S → IsKStableSub ε E S' → S' = ⊥ ∨ S' = S) ∧
      ∃ w ∈ S, w ≠ 0 ∧ IsKHWVec ε E μ w := hS
  obtain ⟨_, hSt, hirr, _⟩ := hS'
  have hx1 : (∀ a, E a a x = (μ a : ℂ) • x) ∧ ∀ a b, a < b → ε a = ε b → E a b x = 0 := hxw
  have hle : kLowSpan ε E y ≤ S := kLowSpan_le hSt hy
  have heq : kLowSpan ε E y = S := by
    rcases hirr _ hle (kLowSpan_kStable hE hyw) with h | h
    · exfalso
      apply hy0
      have hmem : y ∈ kLowSpan ε E y := self_mem_kLowSpan y
      rw [h] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    · exact h
  exact kLowSpan_line hE hU hyw hy0 (by rw [heq]; exact hx) hx1.1
end ReciprocityTheory.ChartRestriction.DS
