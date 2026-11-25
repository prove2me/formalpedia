-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:18.876731+00:00
-- url     : https://prove2.me/submissions/9ae73e8a-aa68-4645-b92a-c25c843b19d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_neg

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
variable (b : ℤ) (d : ℕ)
variable {b d}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t - t') := by
  rw [sub_eq_add_neg]
  exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add h (PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg h')
end PI.UnitaryGroupMassFormula.UnimodLocStd
