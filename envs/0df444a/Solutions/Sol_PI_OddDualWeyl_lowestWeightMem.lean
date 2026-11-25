-- Prove2me | solution 1 for PI.OddDualWeyl.lowestWeightMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:33.788344+00:00
-- url     : https://prove2.me/submissions/f9e48d76-7139-452c-82fc-f75c5302613d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_hw_mem
import Theorems.Thm_PI_OddDualWeyl_Low_pw_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
namespace PI.OddDualWeyl
theorem _root_.solution : LowMem := by
  intro R _ k ν
  cases k with
  | zero =>
    have : low R ν = hw R (le_refl 0) ν := by simp [low, pw, hw]
    rw [this]; exact Low.hw_mem _ _
  | succ n => exact Low.pw_mem ν _
end PI.OddDualWeyl
