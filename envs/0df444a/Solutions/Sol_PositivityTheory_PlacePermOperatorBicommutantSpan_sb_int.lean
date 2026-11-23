-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:53.451229+00:00
-- url     : https://prove2.me/submissions/5818bf3d-fc92-451e-a5c4-36ae6ed8164b

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset

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
theorem _root_.solution {φ : V → ℂ} (hφ : SB φ) : Integrable φ μ := by
  obtain ⟨_, _, _, _, _, _, -⟩ := h
  exact hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
end PositivityTheory.PlacePermOperatorBicommutantSpan
