-- Prove2me | solution 1 for PI.ZW.isPrimitive_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:33.240306+00:00
-- url     : https://prove2.me/submissions/f4407895-e9c5-4d82-bcf6-9abab4d1127e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact (DirichletCharacter.isPrimitive_def χ).mp hχ
end PI.ZW
