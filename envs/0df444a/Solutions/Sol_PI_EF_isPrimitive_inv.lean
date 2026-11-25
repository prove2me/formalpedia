-- Prove2me | solution 1 for PI.EF.isPrimitive_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:09.143334+00:00
-- url     : https://prove2.me/submissions/381072b2-ed5e-4dcb-9103-0b97c0ddf85f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Theorems.Thm_PI_EF_conductor_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ}
namespace PI.EF
theorem _root_.solution {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  have h' : χ.conductor = N := h
  show (χ⁻¹).conductor = N
  rw [conductor_inv, h']
end PI.EF
