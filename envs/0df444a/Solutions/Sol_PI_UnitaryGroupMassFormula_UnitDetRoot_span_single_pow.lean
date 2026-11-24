-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.span_single_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:12.686208+00:00
-- url     : https://prove2.me/submissions/c9e3b591-7628-4174-81c1-44c84e6f1bf8

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
theorem _root_.solution (x : ℂ) (n : ℕ) : span (𝓞 F) {x} ^ n = span (𝓞 F) {x ^ n} := by
  rw [span_pow, Set.singleton_pow]
end PI.UnitaryGroupMassFormula.UnitDetRoot
