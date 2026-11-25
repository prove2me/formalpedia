-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.CO.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:54.559124+00:00
-- url     : https://prove2.me/submissions/ce6ec847-828c-454d-9d00-8246e05e09f0

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
variable [IsTopologicalAddGroup V]
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
namespace CO
theorem _root_.solution {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') :=
  ⟨by rw [AddSubgroup.add_normal]; exact h.1.add h'.1, AddSubgroup.isOpen_mono le_sup_left h.2⟩
end CO
end PositivityTheory.PlacePermOperatorBicommutantSpan
