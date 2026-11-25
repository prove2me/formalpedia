-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.sigR_dv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:01.551823+00:00
-- url     : https://prove2.me/submissions/2cca00f8-0e01-4b99-8713-1930e6af037b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE

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
theorem _root_.solution (σ : E →ₐ[F] E) (d : 𝓞 F) : PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v d) = dv E v d := by
  simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE, dv]
end PI.UnitaryApproxFinWork
