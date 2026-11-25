-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_algebraMap_bed52a5ed15c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:36.605533+00:00
-- url     : https://prove2.me/submissions/f46e98c7-9339-48f9-96a4-09568c34fa93

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
    (toSub h t e).comp (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc W t e) :=
  RingHom.ext fun _ => rfl
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
