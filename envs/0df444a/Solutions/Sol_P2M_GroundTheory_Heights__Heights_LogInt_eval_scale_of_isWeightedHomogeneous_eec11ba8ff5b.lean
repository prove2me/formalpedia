-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_eval_scale_of_isWeightedHomogeneous_eec11ba8ff5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:15.128661+00:00
-- url     : https://prove2.me/submissions/8cd71a97-ccaf-4cda-95e4-91d446e56800

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_prod_scaleP_fcddd27cbced


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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution {ι : Type*} (p : ι → Prop) [DecidablePred p] (a : ℂ) (v : ι → ℂ)
    (g : MvPolynomial ι ℂ) (d : ℕ) (hg : IsWeightedHomogeneous (indW p) g d) :
    eval (scaleP p a v) g = a ^ d * eval v g := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [prod_scaleP, hg (mem_support_iff.mp hm)]
  ring
end GroundTheory.Heights₂.Heights.LogInt
