-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpA.om_of_omS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:24.756946+00:00
-- url     : https://prove2.me/submissions/737aa059-cffc-4ef0-8393-889eb4436b6f

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_continuous
import Theorems.Thm_PositivityTheory_ThKR_Mp_om_sch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA
namespace PositivityTheory.ThKR.Mp.MpA
theorem _root_.solution {g : G l} {c : ℂ} (hc : ∀ f, omS g f = c • f) (F : L2 l) : om g F = c • F := by
  refine dense_sch.induction_on (p := fun F => om g F = c • F) F
    (isClosed_eq (om g).continuous (continuous_const_smul c)) fun f => ?_
  rw [om_sch, hc, map_smul]
end PositivityTheory.ThKR.Mp.MpA
