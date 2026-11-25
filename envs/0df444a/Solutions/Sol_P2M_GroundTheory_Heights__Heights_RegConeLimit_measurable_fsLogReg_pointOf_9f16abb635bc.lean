-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegConeLimit_measurable_fsLogReg_pointOf_9f16abb635bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:04.413316+00:00
-- url     : https://prove2.me/submissions/24e3cdc4-fca4-4504-adf1-b61d005ce27e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegConeLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f


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
open MvPolynomial MeasureTheory Filter Topology Set ConeFsLog
noncomputable section
open GroundTheory.Heights₂.Heights.RegConeLimit
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RegConeLimit
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable fun y : EuclideanSpace ℂ (Fin n) => fsLogReg h u ε (h.pointOf y) := by
  have : (fun y : EuclideanSpace ℂ (Fin n) => fsLogReg h u ε (h.pointOf y)) = fun y =>
      Real.log ((‖∑ j, u j * h.pointOf y j‖ ^ 2 + ε * ‖y‖ ^ 2) / ‖y‖ ^ 2) / 2 := by
    funext y; rw [fsLogReg, dualNorm_pointOf]
  rw [this]
  have hp : Continuous fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y := by
    unfold HermNorm.pointOf
    fun_prop
  have hs : Continuous fun y : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * h.pointOf y j‖ :=
    (continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)).norm
  refine (Real.measurable_log.comp (Measurable.div ?_ ?_)).div_const 2
  · exact ((hs.pow 2).add (continuous_const.mul (continuous_norm.pow 2))).measurable
  · exact (continuous_norm.pow 2).measurable
end GroundTheory.Heights₂.Heights.RegConeLimit
