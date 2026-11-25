-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.dv_mem_Sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:21.105225+00:00
-- url     : https://prove2.me/submissions/3890e584-8ef0-406d-ad54-c60232ba68eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Theorems.Thm_PI_UnitaryApproxFinWork_algebraMap_mem_intOE
import Theorems.Thm_PI_UnitaryApproxFinWork_inclE_mem_Sv

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) : dv E v d ∈ Sv E v := inclE_mem_Sv v (algebraMap_mem_intOE d)
end PI.UnitaryApproxFinWork
