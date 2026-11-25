-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.co_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:47.77522+00:00
-- url     : https://prove2.me/submissions/e156c39b-d4bd-43e5-b48c-2a1943056d6e

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_CO_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (h : NADual V χ μ) {K : Set V} (hK : IsCompact K) : ∃ L : AddSubgroup V, CO L ∧ K ⊆ L := by
  obtain ⟨_, -, -, -, -, -, -, hbig, -⟩ := h
  refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, CO L ∧ s ⊆ L) ?_ ?_ ?_ ?_
  · obtain ⟨L, h1, h2, -⟩ := hbig 0
    exact ⟨L, ⟨h1, h2⟩, empty_subset _⟩
  · rintro s t hst ⟨L, h1, h2⟩
    exact ⟨L, h1, hst.trans h2⟩
  · rintro s t ⟨L, h1, h2⟩ ⟨L', h1', h2'⟩
    exact ⟨L ⊔ L', h1.sup h1', union_subset (h2.trans (SetLike.coe_subset_coe.2 le_sup_left))
      (h2'.trans (SetLike.coe_subset_coe.2 le_sup_right))⟩
  · intro x _
    obtain ⟨L, h1, h2, h3⟩ := hbig x
    exact ⟨L, mem_nhdsWithin_of_mem_nhds (h2.mem_nhds h3), L, ⟨h1, h2⟩, le_rfl⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan
