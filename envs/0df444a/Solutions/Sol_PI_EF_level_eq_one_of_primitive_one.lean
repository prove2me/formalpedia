-- Prove2me | solution 1 for PI.EF.level_eq_one_of_primitive_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:35.029408+00:00
-- url     : https://prove2.me/submissions/d442d55a-40fe-4df7-9118-0ba434358334

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB

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
theorem _root_.solution [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive)
    (h1 : χ = 1) : N = 1 := by
  have h' : χ.conductor = N := h
  rw [h1, DirichletCharacter.conductor_one] at h'
  exact h'.symm
end PI.EF
