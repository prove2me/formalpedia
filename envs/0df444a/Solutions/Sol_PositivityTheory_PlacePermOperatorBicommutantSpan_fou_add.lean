-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.fou_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:03.80517+00:00
-- url     : https://prove2.me/submissions/c066c67d-2b21-48ee-9ee7-bb52a8b6071c

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_int
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_chi

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
theorem _root_.solution {f g : V → ℂ} (hf : SB f) (hg : SB g) : fou χ μ (f + g) = fou χ μ f + fou χ μ g := by
  funext y
  simp only [fou, Pi.add_apply, add_mul]
  exact integral_add (sb_int h (sb_chi h hf y)) (sb_int h (sb_chi h hg y))
end PositivityTheory.PlacePermOperatorBicommutantSpan
