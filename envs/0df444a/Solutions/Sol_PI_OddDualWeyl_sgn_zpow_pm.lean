-- Prove2me | solution 1 for PI.OddDualWeyl.sgn_zpow_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:14.784394+00:00
-- url     : https://prove2.me/submissions/f141e89a-99d7-43bf-a627-01a1a039247f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

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
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution (hS : SgnPM) (m : ℕ) (n : ℤ) : sgnK K m ^ n = 1 ∨ sgnK K m ^ n = -1 := by
  rcases hS K m with h | h
  · left
    rw [h, _root_.one_zpow]
  · rw [h]
    rcases Int.even_or_odd n with he | ho
    · left
      exact he.neg_one_zpow
    · right
      exact ho.neg_one_zpow
end PI.OddDualWeyl
