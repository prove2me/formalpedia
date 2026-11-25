-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.cT_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:07.438108+00:00
-- url     : https://prove2.me/submissions/19bc3595-e4b4-48d2-98a2-5fedb60c7d7e

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
theorem _root_.solution (σ : E →ₐ[F] E) (M : Matrix n n E) :
    PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (M.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      (PI.UnitaryApproxDefs.cT (σ : E →+* E) M).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]
end PI.UnitaryApproxFinWork
