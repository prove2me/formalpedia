-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_mat_ne_zero_8bce070c40f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:42.084799+00:00
-- url     : https://prove2.me/submissions/6e56f8d3-f792-48eb-869d-ee938c134c28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere

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
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.HermNorm
theorem _root_.solution (h : HermNorm n) (l : Fin n) : ∃ j, h.mat l j ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h.isUnit_det.ne_zero (Matrix.det_eq_zero_of_row_eq_zero l hc)
end GroundTheory.Heights₂.Heights.HermNorm
