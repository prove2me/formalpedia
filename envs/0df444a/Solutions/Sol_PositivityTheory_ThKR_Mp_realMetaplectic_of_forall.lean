-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.realMetaplectic_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:41.011827+00:00
-- url     : https://prove2.me/submissions/e7165761-a57f-47ea-a953-aa4c9d8b5262

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Theorems.Thm_PositivityTheory_ThKR_Mp_om_sch
import Theorems.Thm_PositivityTheory_ThKR_Mp_om_rho
import Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_om

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution
    (h : ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l], Mp.TopG l ∧ Mp.Cover l ∧ Mp.Surj l ∧ Mp.Ker l ∧
      Mp.Smooth l ∧ Mp.OnePar l) : GlobalTheory.Published.RealMetaplecticRepresentation := fun l _ _ _ => by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h l
  exact ⟨Mp.G l, inferInstance, inferInstance, h1, Mp.pr, Mp.om, Mp.omS, ⟨h2, h3, h4⟩,
    Mp.continuous_om, Mp.om_rho, Mp.om_sch, h5, h6⟩
end PositivityTheory.ThKR.Mp
