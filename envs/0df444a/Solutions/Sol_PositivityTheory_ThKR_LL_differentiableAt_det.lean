-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.differentiableAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:34.479658+00:00
-- url     : https://prove2.me/submissions/7c1252ce-3a91-45f2-9fb9-41ee7046bada

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {M : ℝ → Matrix l l ℝ} {t : ℝ} (h : ∀ i j, DifferentiableAt ℝ (fun t => M t i j) t) :
    DifferentiableAt ℝ (fun t => (M t).det) t := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ => (DifferentiableAt.fun_finset_prod fun i _ => h _ _).const_mul _
end PositivityTheory.ThKR.LL
