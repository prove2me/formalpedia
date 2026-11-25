-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:29.56691+00:00
-- url     : https://prove2.me/submissions/d11f675e-7134-41f5-a24e-07036d8fd64d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepPrimPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepRepModl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepNewton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepRamDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSmulRight

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
theorem _root_.solution (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m (ξ • u) v = ξ * stdH L m u v := by
  first
  | (simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
end PI.UnitaryGroupMassFormula.UnimodLocStd
