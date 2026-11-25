-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_chartX_map_2fbd012a6e92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:04.875836+00:00
-- url     : https://prove2.me/submissions/258152c7-3f27-4316-a371-2b6ff8767be5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_chartX_68197c518427

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
    (W.map (chartX I t e)).comap (chartX I t e) = RingHom.ker (chartX W t e) := by
  rw [← ker_toSub h t, RingHom.comap_ker, toSub_comp_chartX]
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
