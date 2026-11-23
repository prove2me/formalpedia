-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.mem_intOE_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:08.862806+00:00
-- url     : https://prove2.me/submissions/92391bb5-7634-447c-9372-493cf208b41d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral

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
theorem _root_.solution {x : E} (h : IsIntegral ℤ x) : x ∈ PI.UnitaryApproxDefs.intOE E := RingHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩
end PI.UnitaryApproxFinWork
