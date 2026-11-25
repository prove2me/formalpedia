-- Prove2me | solution 1 for PI.ZW.log_le_nine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:03.616388+00:00
-- url     : https://prove2.me/submissions/e47850fe-764d-4e1b-bd41-e9004eb6596d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution (X M' : ℝ) (hX : 2 ≤ X) (hM : 0 < M') (h : M' ≤ 170 * X) :
    Real.log M' ≤ 9 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have h170 : Real.log 170 ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  calc Real.log M' ≤ Real.log (170 * X) := Real.log_le_log hM h
    _ = Real.log 170 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    _ ≤ 9 * Real.log X := by linarith
end PI.ZW
