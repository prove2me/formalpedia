-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_PP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:21.07421+00:00
-- url     : https://prove2.me/submissions/a75a2df7-b3dd-4195-8816-742d12d0ea22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_mul
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution : DiffLoc_P (E := E) v * DiffLoc_P (E := E) v = DiffLoc_P (E := E) v := by
  rw [← DiffLoc_psi_one, ← DiffLoc_psi_mul, mul_one]
end PI.LocFramePrimWork
