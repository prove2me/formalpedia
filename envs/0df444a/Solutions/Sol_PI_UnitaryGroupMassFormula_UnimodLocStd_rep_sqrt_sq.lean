-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sqrt_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:23.228444+00:00
-- url     : https://prove2.me/submissions/1ec8aa2d-18b0-4d74-ac6f-5b5f68a988aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d), Complex.ofReal_natCast]
end PI.UnitaryGroupMassFormula.UnimodLocStd
