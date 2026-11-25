-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logReg_zero_ca923fd2cacc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:51.471148+00:00
-- url     : https://prove2.me/submissions/2c6e2109-e183-4cf4-b873-64e9618500c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (u : Fin n → ℂ) (x : Fin n → ℂ) :
    logReg u 0 x = Real.log ‖linEval u x‖ := by
  unfold logReg
  rw [add_zero, Real.log_pow]
  push_cast
  ring
end GroundTheory.Heights₂.Heights
