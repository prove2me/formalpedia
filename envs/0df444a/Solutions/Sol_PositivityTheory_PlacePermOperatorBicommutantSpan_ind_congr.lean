-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.ind_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:09.655141+00:00
-- url     : https://prove2.me/submissions/c3fdeea3-f881-4e75-8adb-228c078e78a5

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_not

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
omit [TopologicalSpace V]
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {a b x y : V} {L L' : AddSubgroup V} (h : x - a ∈ L ↔ y - b ∈ L') : ind a L x = ind b L' y := by
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (h.1 hx)]
  · rw [ind_of_not hx, ind_of_not (mt h.2 hx)]
end PositivityTheory.PlacePermOperatorBicommutantSpan
