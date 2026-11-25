-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_chartX_68197c518427
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:21.422703+00:00
-- url     : https://prove2.me/submissions/1d6cef73-874f-4d94-8127-ddad6199ddd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals

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
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMaxIdeals
theorem _root_.solution {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (toSub h t e).comp (chartX I t e) = chartX W t e :=
  RingHom.ext fun _ => rfl
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
