-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_halfGauss_lt_top_d8f4b704046d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:30.03282+00:00
-- url     : https://prove2.me/submissions/de1f28c5-de4b-454c-9b6b-6a458a4fc26b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution : halfGauss < ∞ := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (1 / 2 : ℂ))
    (by norm_num) 0 0).norm
  have h2 : Integrable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2 / 2))) := by
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.norm_exp]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  exact h2.lintegral_lt_top
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
