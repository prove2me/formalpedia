-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_kappa_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:10.836803+00:00
-- url     : https://prove2.me/submissions/f95226a9-daca-4bb2-901f-0a765a45d758

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_area_ne

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
theorem _root_.solution : repKappa a b d ha hd lam hlam ≠ 0 := by
  unfold repKappa
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.2 (rep_area_ne a b d ha hd lam hlam)))
    (Complex.ofReal_ne_zero.2 (Complex.normSq_pos.2 hlam).ne')) (Nat.cast_ne_zero.2 ha.ne')
end PI.UnitaryGroupMassFormula.UnimodLocStd
