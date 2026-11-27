-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartPointLine__L_one_ne_zero_46ab1c904230
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:07:50.079598+00:00
-- url     : https://prove2.me/submissions/c9df31d0-a9f7-49e5-b583-99f068071c96

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
theorem _root_.solution : ηL 1 ≠ 0 := by simp [ηL]
end GroundTheory.Heights₂.Heights.ChartPointLine
