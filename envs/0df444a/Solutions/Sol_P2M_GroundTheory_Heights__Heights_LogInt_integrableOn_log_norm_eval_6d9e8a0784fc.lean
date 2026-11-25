-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:35.305557+00:00
-- url     : https://prove2.me/submissions/4f857fd0-2d78-4282-b4f7-0ab1a4b045d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logPoly_488db128c6da

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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) (r : ℝ) :
    IntegrableOn (fun u => Real.log ‖eval u g‖) (polydisc ι r) := by
  classical
  exact (logPoly r _ g rfl hg).1
end GroundTheory.Heights₂.Heights.LogInt
