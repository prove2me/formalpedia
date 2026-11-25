-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.idS_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:34.068724+00:00
-- url     : https://prove2.me/submissions/1dadeddb-b0fe-4aef-ac38-8e513a9442d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
import Theorems.Thm_PI_InvIdealIdxPiWork_idS_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace PI.InvIdealIdxPiWork
theorem _root_.solution {I I' : Ideal (𝓞 E)} (h : I ≤ I') : idS (E := E) I ≤ idS I' := by
  rw [idS_eq_map, idS_eq_map]
  exact AddSubgroup.map_mono (by intro x hx; exact h hx)
end PI.InvIdealIdxPiWork
