-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_primG_eq_646b67a09f3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:22.943776+00:00
-- url     : https://prove2.me/submissions/9e608fd1-284d-4dbd-82b0-616eac69675b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a

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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) (s : ℝ) : primG m s = polyP m s * (s * log s) - polyR m s := by
  rw [primG, ← mul_polyP]
  ring
end GroundTheory.Heights₂.Heights.SphereMean
