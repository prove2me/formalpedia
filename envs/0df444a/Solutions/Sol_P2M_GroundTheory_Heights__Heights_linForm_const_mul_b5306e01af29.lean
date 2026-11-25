-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linForm_const_mul_b5306e01af29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:27.976347+00:00
-- url     : https://prove2.me/submissions/69194267-cd91-460e-8c2f-5b2c845654de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAENrm

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : ℂ) (v : Fin n → ℂ) :
    linForm (fun j => c * v j) = C c * linForm v := by
  simp only [linForm, Finset.mul_sum, map_mul, mul_assoc]
end GroundTheory.Heights₂.Heights
