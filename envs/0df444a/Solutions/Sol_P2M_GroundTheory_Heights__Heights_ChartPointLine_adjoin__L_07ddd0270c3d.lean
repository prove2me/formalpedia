-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartPointLine_adjoin__L_07ddd0270c3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:30.714266+00:00
-- url     : https://prove2.me/submissions/5a6d2679-9d7e-456f-98f6-3c3ee14babe7

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
theorem _root_.solution : IntermediateField.adjoin KL (Set.range ηL) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin KL (Set.range ηL)) x
end GroundTheory.Heights₂.Heights.ChartPointLine
