-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.chi_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:54.440224+00:00
-- url     : https://prove2.me/submissions/06a0c3d7-b0cd-4e80-b249-232200960b69

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_lc_of_inv
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_co_cpt
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_co_perp

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
variable (h : NADual V χ μ)
include h
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (a : V) : IsLocallyConstant fun y => χ a y := by
  have := h.1
  obtain ⟨L, hL, ha⟩ := co_cpt h (isCompact_singleton (x := a))
  exact lc_of_inv (co_perp h hL).2 fun x l hl => by rw [chi_add' h, hl a (ha rfl), mul_one]
end PositivityTheory.PlacePermOperatorBicommutantSpan
