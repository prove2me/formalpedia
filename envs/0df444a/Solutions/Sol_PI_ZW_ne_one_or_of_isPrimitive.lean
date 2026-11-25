-- Prove2me | solution 1 for PI.ZW.ne_one_or_of_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:16:04.223697+00:00
-- url     : https://prove2.me/submissions/2b487ff5-f283-4c97-9e9a-5a78138903e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ ≠ 1 ∨ N = 1 := by
  by_cases h : χ = 1
  · right
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hχ
    exact hχ.symm
  · exact Or.inl h
end PI.ZW
