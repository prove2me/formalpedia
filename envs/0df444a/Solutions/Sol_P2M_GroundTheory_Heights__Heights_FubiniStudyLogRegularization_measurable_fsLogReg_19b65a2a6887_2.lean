-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_measurable_fsLogReg_19b65a2a6887
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:06.983168+00:00
-- url     : https://prove2.me/submissions/d9910f53-f805-48b5-a366-5a472e339df7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_sqDual_73944ddad90b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb

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
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable (fsLogReg h u ε) := by
  have hf : fsLogReg h u ε = fun y =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 :=
    funext (fsLogReg_eq h u ε)
  rw [hf]
  exact ((Real.measurable_log.comp (((contDiff_lin u).continuous.measurable.add
    (measurable_const.mul (contDiff_sqDual h).continuous.measurable)).div
      (contDiff_sqDual h).continuous.measurable)).div_const 2)
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
