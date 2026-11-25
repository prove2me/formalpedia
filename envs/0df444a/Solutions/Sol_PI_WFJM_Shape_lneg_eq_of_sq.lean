-- Prove2me | solution 1 for PI.WFJM.Shape.lneg_eq_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:39.337799+00:00
-- url     : https://prove2.me/submissions/6dc49295-dc4f-452f-8768-3f8900448d22

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
theorem _root_.solution {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lneg α = lneg β := by
  obtain ⟨hmk, _, hd⟩ := h
  unfold lneg
  congr 1
  apply List.ext_getElem (by simp [hmk])
  intro t h1 h2
  simp only [List.getElem_ofFn]
  rw [hd ⟨t, by simpa using h1⟩ ⟨t, by simpa using h2⟩ rfl]
end PI.WFJM.Shape
