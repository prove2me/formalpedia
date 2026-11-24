-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.kappa_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:49.822917+00:00
-- url     : https://prove2.me/submissions/e62ac383-05a8-4b57-9f81-8affa8c10df4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : conj (repKappa a b d ha hd lam hlam) = repKappa a b d ha hd lam hlam := by
  unfold repKappa
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_natCast]
end PI.UnitaryGroupMassFormula.UnimodLocStd
