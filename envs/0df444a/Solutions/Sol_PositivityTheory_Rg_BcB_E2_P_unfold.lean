-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:46.363632+00:00
-- url     : https://prove2.me/submissions/54791195-f678-40da-9e1f-7ab9311e0e0c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Unfold
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Unfold_unfolded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : KerBasic → ConvCont → Unfold := by
  intro hk hc X φ u hφ hu hinv
  exact ⟨fun x => Unfold.unfolded hk X φ u hφ hu hinv x, hc X φ u hφ hu.locallyIntegrable⟩
end PositivityTheory.Rg.BcB.E2.P
