-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:52.526651+00:00
-- url     : https://prove2.me/submissions/201410c2-4a6a-42cb-a2e1-44955ac57ddd

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
omit [AddCommGroup V]
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {f g : V → ℂ} (hf : SB f) (hg : SB g) : SB (f + g) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan
