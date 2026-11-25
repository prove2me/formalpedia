-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.iso_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:56.63947+00:00
-- url     : https://prove2.me/submissions/fd8851b0-7911-410a-bf41-b47aa1878d34

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_ph
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_dil
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_fou
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ^ 2 = |Ai.det|) :
    Iso (big Ai B C c) :=
  (iso_ph _).mul ((iso_dil h hc).mul (iso_fou.mul ((iso_ph _).mul iso_fouInv)))
end PositivityTheory.ThKR.LL
