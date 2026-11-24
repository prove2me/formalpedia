-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.span_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:06:11.777869+00:00
-- url     : https://prove2.me/submissions/c0441b8d-10fa-41c7-80d3-489e8bc9184a

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
theorem _root_.solution (x y : ℂ) : span (𝓞 F) {x} * span (𝓞 F) {y} = span (𝓞 F) {x * y} := by
  rw [span_mul_span, Set.singleton_mul_singleton]
end PI.UnitaryGroupMassFormula.UnitDetRoot
