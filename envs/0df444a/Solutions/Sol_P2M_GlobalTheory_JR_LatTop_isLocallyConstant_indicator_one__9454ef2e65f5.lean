-- Prove2me | solution 1 for P2M_GlobalTheory_JR_LatTop_isLocallyConstant_indicator_one__9454ef2e65f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:13.496912+00:00
-- url     : https://prove2.me/submissions/c2fd2d61-c0a9-43a4-b5e1-bd2082d04ba9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianLatticeIsOpenIsCompactTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LatTop
namespace GlobalTheory.JR.LatTop
theorem _root_.solution {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
end GlobalTheory.JR.LatTop
