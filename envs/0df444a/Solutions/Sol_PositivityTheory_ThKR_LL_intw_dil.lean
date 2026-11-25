-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.intw_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:04.446356+00:00
-- url     : https://prove2.me/submissions/3beacdfd-0710-4ea5-bed3-458ee95805d7

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_dil_apply

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
theorem _root_.solution {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {p q p' q' : Eu l} (hp : B p' = p) (hq : ∀ x, ⟪q', x⟫ = ⟪q, B x⟫) :
    Intw (dil B) p q p' q' := fun f g h => by
  funext x
  simp only [rf, dil_apply hB, h, map_add, hp, real_inner_comm q' p', hq, real_inner_comm q p]
end PositivityTheory.ThKR.LL
