-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.H_nsmul_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:49.145321+00:00
-- url     : https://prove2.me/submissions/f7bd5699-6f75-4ef1-9d4b-519b9579080b

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
theorem _root_.solution (L : PeriodPair) (s t : ℕ) (v w : m → ℂ) :
    stdH L m (s • v) (t • w) = (s : ℂ) * t * stdH L m v w := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Pi.mul_apply, Pi.natCast_apply, map_mul, map_natCast]
    ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
