-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LowSmooth.finStable_directed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:31.794847+00:00
-- url     : https://prove2.me/submissions/9f27a512-5091-449d-99b2-21e9b3fea7b6

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
theorem _root_.solution (G : Set ι) (ρ : ι → H →L[ℂ] H) :
    DirectedOn (· ≤ ·) (FinStable G ρ) := by
  intro S hS T hT
  refine ⟨S ⊔ T, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · haveI := hS.1
    haveI := hT.1
    infer_instance
  · intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hS.2 g hg y hy) (hT.2 g hg z hz)
end PI.UnitaryGroupMassFormula.LowSmooth
