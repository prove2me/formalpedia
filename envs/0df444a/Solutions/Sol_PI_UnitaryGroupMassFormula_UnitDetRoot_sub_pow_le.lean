-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:41.276697+00:00
-- url     : https://prove2.me/submissions/67726b43-c6c6-450b-b253-f6ecb5a6a29d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField nonZeroDivisors
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
variable (F : IntermediateField ℚ ℂ)
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {S T : Submodule (𝓞 F) ℂ} (h : S ≤ T) (n : ℕ) : S ^ n ≤ T ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_le_mul' ih h
end PI.UnitaryGroupMassFormula.UnitDetRoot
