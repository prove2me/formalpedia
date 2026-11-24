-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_theta_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:19:16.314445+00:00
-- url     : https://prove2.me/submissions/90b3a2b8-0c92-4b28-bd16-0f1cc52b1254

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sqrt_sq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_conj_theta

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
theorem _root_.solution (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * conj (cmTheta b d) = (a : ℂ) * c := by
  have h4 : ((4 * (a : ℤ) * c : ℤ) : ℂ) = ((b ^ 2 + d : ℤ) : ℂ) := by rw [hOK]
  push_cast at h4
  have hs := rep_sqrt_sq d
  rw [rep_conj_theta b d, cmTheta]
  linear_combination (-1 / 4 : ℂ) * h4 - (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq +
    (1 / 4 : ℂ) * hs
end PI.UnitaryGroupMassFormula.UnimodLocStd
