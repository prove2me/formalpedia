-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpE.isInducing_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:12.304579+00:00
-- url     : https://prove2.me/submissions/34876f2a-f64a-4997-856e-177e36e878f6

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space

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
open MpE
open PositivityTheory.ThKR.Mp.MpE
namespace PositivityTheory.ThKR.Mp.MpE
theorem _root_.solution :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := ⟨rfl⟩
end PositivityTheory.ThKR.Mp.MpE
