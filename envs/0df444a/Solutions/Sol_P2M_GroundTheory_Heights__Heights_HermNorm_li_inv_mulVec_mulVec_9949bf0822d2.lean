-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_li_inv_mulVec_mulVec_9949bf0822d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:25:22.285946+00:00
-- url     : https://prove2.me/submissions/096b17f4-fa64-42b0-be1e-f6937e044d9b

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
theorem _root_.solution (h : HermNorm n) (v : Fin n → ℂ) : h.mat⁻¹ *ᵥ (h.mat *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det, Matrix.one_mulVec]
end GroundTheory.Heights₂.Heights.HermNorm
