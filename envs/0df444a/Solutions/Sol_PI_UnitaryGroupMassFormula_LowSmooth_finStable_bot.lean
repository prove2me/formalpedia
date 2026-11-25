-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LowSmooth.finStable_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:09.569685+00:00
-- url     : https://prove2.me/submissions/5fff0a96-4189-4b64-8739-37ed8a705f3a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LowSmooth
open PI.UpqRep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*}
namespace PI.UnitaryGroupMassFormula.LowSmooth
theorem _root_.solution (G : Set ι) (ρ : ι → H →L[ℂ] H) : (⊥ : Submodule ℂ H) ∈ FinStable G ρ := by
  refine ⟨inferInstance, fun g _ x hx => ?_⟩
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]
end PI.UnitaryGroupMassFormula.LowSmooth
