-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.norm_exp_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:08.18073+00:00
-- url     : https://prove2.me/submissions/a175b01c-49f9-4c24-97fa-2da4e4530ab3

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution (a b : ℝ) : ‖exp ((a : ℂ) * I) - exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have : exp ((a : ℂ) * I) - exp ((b : ℂ) * I) = exp ((b : ℂ) * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le
end PositivityTheory.ThKR.LL
