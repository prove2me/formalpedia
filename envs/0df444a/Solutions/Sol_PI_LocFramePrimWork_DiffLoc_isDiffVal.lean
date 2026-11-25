-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_isDiffVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:53.579647+00:00
-- url     : https://prove2.me/submissions/05e0dbf7-152a-499f-9f85-4dd5fafa4851

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_exists

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
theorem _root_.solution : IsDiffVal v (dV v) := by
  have h := DiffLoc_exists v
  unfold dV
  rw [dif_pos h]
  exact h.choose_spec
end PI.LocFramePrimWork
