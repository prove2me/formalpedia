-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:02.686212+00:00
-- url     : https://prove2.me/submissions/0d749596-abd5-47f4-8cf3-4d6052247a7e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_finStable_bot
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_finStable_directed

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
theorem _root_.solution (G : Set ι) (ρ : ι → H →L[ℂ] H) {F : Set (Submodule ℂ H)}
    (hF : F ⊆ FinStable G ρ) {x : H} (hx : x ∈ sSup F) : ∃ S ∈ FinStable G ρ, x ∈ S := by
  have hx' : x ∈ sSup (FinStable G ρ) := sSup_le_sSup hF hx
  exact (Submodule.mem_sSup_of_directed ⟨⊥, finStable_bot G ρ⟩ (finStable_directed G ρ)).mp hx'
end PI.UnitaryGroupMassFormula.LowSmooth
