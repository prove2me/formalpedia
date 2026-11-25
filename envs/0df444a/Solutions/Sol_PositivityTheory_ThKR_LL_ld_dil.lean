-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.ld_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:09.687231+00:00
-- url     : https://prove2.me/submissions/4ba7a217-3dac-4587-a3f6-9c8605e638cf

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Theorems.Thm_PositivityTheory_ThKR_LL_ld_dil_one
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
theorem _root_.solution {B : ℝ → Eu l →L[ℝ] Eu l} {B' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt B B' t₀) (h0 : IsUnit (B t₀)) :
    LD (fun t => dil (B t)) (fun f => vf (Ring.inverse (B t₀) * B') (dil (B t₀) f)) t₀ := fun f => by
  refine ld_dil_one (h.const_mul (Ring.inverse (B t₀))) (Ring.inverse_mul_cancel _ h0) _ ?_
  filter_upwards [h.continuousAt.eventually (Units.isOpen.mem_nhds h0)] with t ht x
  rw [dil_apply ht, dil_apply h0, ← ContinuousLinearMap.mul_apply, ← mul_assoc, Ring.mul_inverse_cancel _ h0, one_mul]
end PositivityTheory.ThKR.LL
