-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:05.681621+00:00
-- url     : https://prove2.me/submissions/a45e55c0-7a30-4251-bbd4-8a130461d54d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic

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
variable (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (z w : m → ℂ) :
    stdH L m z w = ((area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
end PI.UnitaryGroupMassFormula.UnimodLocStd
