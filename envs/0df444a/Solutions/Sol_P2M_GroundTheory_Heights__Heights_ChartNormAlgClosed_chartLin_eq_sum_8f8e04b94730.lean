-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_eq_sum_8f8e04b94730
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:38.013804+00:00
-- url     : https://prove2.me/submissions/ebeaaadd-3ab5-4e15-9173-134cea7dd3b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartNormAlgClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_tower_bc962cfa3117
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartX_C_f12160a83ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_localization_C_eccb7f2840c7

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
open GroundTheory.Heights₂.Heights.ChartNormAlgClosed
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]
namespace GroundTheory.Heights₂.Heights.ChartNormAlgClosed
theorem _root_.solution (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by
  simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, algebraMap_tower, chartX_C]
end GroundTheory.Heights₂.Heights.ChartNormAlgClosed
