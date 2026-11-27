-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartPointLine_chart__L_bda12aec8086
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:02:40.769318+00:00
-- url     : https://prove2.me/submissions/65721cf7-389c-46cb-948c-cb2cd29a08e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartPointSeparable

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartPointLine
namespace GroundTheory.Heights₂.Heights.ChartPointLine
theorem _root_.solution : ∑ m, algebraMap ℚ KL (tL m) * ηL m = 1 := by
  simp [Fin.sum_univ_two, tL, ηL]
end GroundTheory.Heights₂.Heights.ChartPointLine
