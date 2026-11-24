-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:46.53664+00:00
-- url     : https://prove2.me/submissions/5cad26b4-205e-4800-adf7-39a9953b4729

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepNewton

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
theorem _root_.solution (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (z : m → ℂ) :
    stdH L m (ξ • z) (ξ • z) = ξ * conj ξ * stdH L m z z := by
  rw [LinearMap.map_smul₂, LinearMap.map_smulₛₗ]
  simp only [smul_eq_mul]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
