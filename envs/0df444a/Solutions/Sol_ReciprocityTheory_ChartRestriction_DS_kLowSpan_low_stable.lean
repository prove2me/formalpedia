-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kLowSpan_low_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:14.761126+00:00
-- url     : https://prove2.me/submissions/f7ba193e-ef96-406d-8054-14a0c0544021

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_mem
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
theorem _root_.solution {y : M} {c d : Fin n} (hcd : IsKLow ε (c, d)) :
    ∀ x ∈ kLowSpan ε E y, E c d x ∈ kLowSpan ε E y := by
  exact mem_kLowSpan_of_map_lowWord_mem (E c d) (fun l hl => lowWord_mem (ε := ε) (E := E) (y := y) (l := (c, d) :: l) (by
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · rw [h]; exact hcd
    · exact hl p h))
end ReciprocityTheory.ChartRestriction.DS
