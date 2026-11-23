-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_swap_of_not_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:42.378241+00:00
-- url     : https://prove2.me/submissions/f314cb4a-89a3-4e92-b500-390e160c10e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {α : Type*} {p : ℕ} (R : Fin p → α) (h : ¬ Function.Injective R) :
    ∃ i j : Fin p, i ≠ j ∧ R ∘ Equiv.swap i j = R := by
  have hex : ∃ i j, R i = R j ∧ i ≠ j := by
    by_contra hc
    push_neg at hc
    exact h fun a b hab => hc a b hab
  obtain ⟨i, j, hij, hne⟩ := hex
  refine ⟨i, j, hne, funext fun k => ?_⟩
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hij]
  · rw [h2, hij]
  · rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
