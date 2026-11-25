-- Prove2me | solution 1 for PI.WFJM.Shape.lpos_eq_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:41.906801+00:00
-- url     : https://prove2.me/submissions/8eb64084-33ec-4e59-b617-8cead3df72ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lpos α = lpos β := by
  obtain ⟨hmk, _, hd⟩ := h
  apply List.ext_getElem (by simp [lpos, hmk])
  intro t h1 h2
  simp only [lpos, List.getElem_ofFn]
  rw [hd ⟨t, by simpa [lpos] using h1⟩ ⟨t, by simpa [lpos] using h2⟩ rfl]
end PI.WFJM.Shape
