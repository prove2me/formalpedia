-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_algebraMap_map_5533eb7a3b9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:59.698301+00:00
-- url     : https://prove2.me/submissions/28d6358b-ad3d-4732-b379-17b40e9eb193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_algebraMap_bed52a5ed15c

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
    (W.map (chartX I t e)).comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc W t e)) := by
  rw [← ker_toSub h t, RingHom.comap_ker, toSub_comp_algebraMap]
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
