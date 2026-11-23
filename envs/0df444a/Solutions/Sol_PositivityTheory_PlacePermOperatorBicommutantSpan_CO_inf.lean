-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.CO.inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:04.125803+00:00
-- url     : https://prove2.me/submissions/212d2f7b-a803-414e-93c2-f0199c06e119

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
theorem _root_.solution {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') :=
  ⟨h.1.inter_right (L'.isClosed_of_isOpen h'), h.2.inter h'⟩
end CO
end PositivityTheory.PlacePermOperatorBicommutantSpan
