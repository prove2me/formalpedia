-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_measurable_fsLogReg_19b65a2a6887
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:05:09.707704+00:00
-- url     : https://prove2.me/submissions/05274235-3b00-414d-a0ae-8f92f818fdd5

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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable (fsLogReg h u ε) := by
  unfold GroundTheory.Heights₂.Heights.fsLogReg HermNorm.dualNorm Matrix.mulVec dotProduct
  fun_prop



