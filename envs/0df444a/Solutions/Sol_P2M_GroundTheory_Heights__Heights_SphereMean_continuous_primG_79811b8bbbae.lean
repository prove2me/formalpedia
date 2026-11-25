-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_continuous_primG_79811b8bbbae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:51.030861+00:00
-- url     : https://prove2.me/submissions/0f4bcc13-6807-47fc-baba-db3ff364dfe6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_primG_eq_646b67a09f3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_continuous_polyP_b22e64d23bf7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_continuous_polyR_113b66fe08f8

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
theorem _root_.solution (m : ℕ) : Continuous (primG m) := by
  have : primG m = fun s => polyP m s * (s * log s) - polyR m s := funext (primG_eq m)
  rw [this]
  exact ((continuous_polyP m).mul continuous_mul_log).sub (continuous_polyR m)
end GroundTheory.Heights₂.Heights.SphereMean
