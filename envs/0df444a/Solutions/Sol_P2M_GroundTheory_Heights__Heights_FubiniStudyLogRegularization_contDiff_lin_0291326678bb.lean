-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:26.803222+00:00
-- url     : https://prove2.me/submissions/35caa9e8-e45f-43f4-b238-9dce6a6a2bd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic

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
theorem _root_.solution (u : Fin n → ℂ) : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
