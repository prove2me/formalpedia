-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.inclE_mem_Sv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:01.464142+00:00
-- url     : https://prove2.me/submissions/11e4192d-011f-46c6-a917-bb5b2d73cf7c

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) :
    PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) x ∈ Sv E v := Subring.subset_closure (Set.mem_union_left _ ⟨⟨x, hx⟩, rfl⟩)
end PI.UnitaryApproxFinWork
