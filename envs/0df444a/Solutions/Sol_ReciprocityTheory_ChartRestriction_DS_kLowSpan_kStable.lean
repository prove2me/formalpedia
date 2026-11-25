-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kLowSpan_kStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:48.862775+00:00
-- url     : https://prove2.me/submissions/87d25412-6ed5-4d1f-80e8-d8a5cedc87e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_mem_of_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_raise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Straight
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
private lemma mem_kLowSpan_of_map_lowWord_mem {y : M} (T : Module.End ℂ M)
    (h : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → T (lowWord E y l) ∈ kLowSpan ε E y) :
    ∀ x ∈ kLowSpan ε E y, T x ∈ kLowSpan ε E y := by
  intro x hx
  have hle : kLowSpan ε E y ≤ (kLowSpan ε E y).comap T := by
    unfold kLowSpan
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact h l hl
  exact hle hx
end Straight
section Unitary
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
end Unitary
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    IsKStableSub ε E (kLowSpan ε E y) := by
  have hy' : (∀ a, E a a y = (μ a : ℂ) • y) ∧ ∀ a b, a < b → ε a = ε b → E a b y = 0 := hy
  intro a b hab
  exact mem_kLowSpan_of_map_lowWord_mem (E a b) (fun l hl => by
    rcases lt_or_ge a b with h | h
    · exact lowWord_raise hE hy l hl a b h hab
    · exact lowWord_mem_of_ge hE hy'.1 hl h hab)
end ReciprocityTheory.ChartRestriction.DS
