-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:51.853943+00:00
-- url     : https://prove2.me/submissions/9b962c24-d42f-484f-b333-82f7776b5418

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
import Theorems.Thm_PI_UnitaryApproxFinWork_map_toS

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
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : M.det ∈ Sv E v := by
  rw [← map_toS hM, ← RingHom.map_det]
  exact (toS hM).det.2
end PI.UnitaryApproxFinWork
