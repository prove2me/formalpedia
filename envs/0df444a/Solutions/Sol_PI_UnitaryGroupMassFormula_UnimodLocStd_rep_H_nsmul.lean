-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:23.051023+00:00
-- url     : https://prove2.me/submissions/6ccb8a26-6b75-44bd-9203-e69de8207a0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact

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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (M : ℕ) (z : m → ℂ) :
    stdH L m (M • z) (M • z) = (M : ℂ) ^ 2 * stdH L m z z := by
  simp only [map_nsmul, LinearMap.smul_apply]
  simp only [nsmul_eq_mul]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
