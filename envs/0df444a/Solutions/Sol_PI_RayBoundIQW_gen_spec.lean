-- Prove2me | solution 1 for PI.RayBoundIQW.gen_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:07.603609+00:00
-- url     : https://prove2.me/submissions/82edf231-2348-4c12-9018-a6c90e5498d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_GenCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open PI PI.RayBoundIQW
variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
namespace PI.RayBoundIQW
theorem _root_.solution (J : PrimeTo qq) :
    Ideal.span {gen qq J} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) :=
  (principal qq J).choose_spec
end PI.RayBoundIQW
