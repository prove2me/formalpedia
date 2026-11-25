-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.one_tmul_mem_Sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:57.093299+00:00
-- url     : https://prove2.me/submissions/0f8f83d6-bb67-412a-bf15-f71c527ee8c4

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletion F}
    (ht : t ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] t ∈ Sv E v := Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)
end PI.UnitaryApproxFinWork
