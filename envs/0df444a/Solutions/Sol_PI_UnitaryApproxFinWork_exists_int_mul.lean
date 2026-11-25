-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.exists_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:48.44271+00:00
-- url     : https://prove2.me/submissions/9b6d2b56-d437-44e7-b825-20d869bb4c5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Theorems.Thm_PI_UnitaryApproxFinWork_exists_nat_mul

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
theorem _root_.solution (x : E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ algebraMap F E (c : F) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  obtain ⟨m, hm, hx⟩ := exists_nat_mul x
  refine ⟨(m : 𝓞 F), by exact_mod_cast hm.ne', ?_⟩
  simpa using hx
end PI.UnitaryApproxFinWork
