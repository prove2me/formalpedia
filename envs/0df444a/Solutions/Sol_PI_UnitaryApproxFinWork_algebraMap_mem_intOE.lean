-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.algebraMap_mem_intOE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:43.389796+00:00
-- url     : https://prove2.me/submissions/d90d656a-56a0-4a3b-80ba-cfcd1d621a3f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Theorems.Thm_PI_UnitaryApproxFinWork_mem_intOE_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (a : 𝓞 F) : algebraMap F E (a : F) ∈ PI.UnitaryApproxDefs.intOE E := mem_intOE_of_isIntegral (IsIntegral.algebraMap (NumberField.RingOfIntegers.isIntegral_coe a))
end PI.UnitaryApproxFinWork
