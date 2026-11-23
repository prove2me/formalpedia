-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:00.028809+00:00
-- url     : https://prove2.me/submissions/5fe5a3db-ff6c-49a5-85ef-5331e0f145fd

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_not
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_lc_of_inv

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
theorem _root_.solution [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by
  refine ⟨lc_of_inv h.2 fun x l hl => ?_, HasCompactSupport.intro (K := (fun y => y + a) '' L)
    (h.1.image (continuous_id.add continuous_const)) fun x hx => ind_of_not fun h' => hx ⟨_, h', by simp⟩⟩
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (by rw [add_sub_right_comm]; exact L.add_mem hx hl)]
  · rw [ind_of_not hx, ind_of_not fun h' => hx (by
      rw [add_sub_right_comm] at h'; exact (L.add_mem_cancel_right hl).1 h')]
end PositivityTheory.PlacePermOperatorBicommutantSpan
