-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:15.880501+00:00
-- url     : https://prove2.me/submissions/9092d18c-2be3-4b04-8aa8-2982e84bac89

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
    ∀ᵐ u ∂(volume.restrict (polydisc ι r)), eval u g ≠ 0 := by
  classical
  exact (logPoly r _ g rfl hg).2
end GroundTheory.Heights₂.Heights.LogInt
