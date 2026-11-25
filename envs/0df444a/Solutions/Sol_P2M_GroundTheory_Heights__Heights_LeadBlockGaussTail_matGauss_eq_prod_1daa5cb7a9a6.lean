-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_matGauss_eq_prod_1daa5cb7a9a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:16.872433+00:00
-- url     : https://prove2.me/submissions/d7121279-d7d9-47c7-a7b2-68391781243d

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
theorem _root_.solution {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    matGauss π = ∏ i, ∏ j, ENNReal.ofReal (Real.exp (-‖π i j‖ ^ 2)) := by
  unfold matGauss
  rw [← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
