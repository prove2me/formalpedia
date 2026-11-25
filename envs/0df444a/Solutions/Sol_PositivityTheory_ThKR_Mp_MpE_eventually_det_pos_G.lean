-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpE.eventually_det_pos_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:23.125829+00:00
-- url     : https://prove2.me/submissions/3f13f073-c608-45d8-82c1-905ffb1e1a50

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_eventually_det_pos
import Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_pr


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
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpE
namespace PositivityTheory.ThKR.Mp.MpE
theorem _root_.solution : ∀ᶠ g in 𝓝 (1 : G l), 0 < (pr g).1.toBlocks₁₁.det := by
  have h := continuous_pr.tendsto (1 : G l)
  rw [map_one] at h
  exact h.eventually eventually_det_pos
end PositivityTheory.ThKR.Mp.MpE
