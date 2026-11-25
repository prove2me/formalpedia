-- Prove2me | solution 1 for PI.EF.Lent_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:01.044956+00:00
-- url     : https://prove2.me/submissions/08ad2bdb-5a7b-466d-94a0-150ca42513b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_Lent_of_ne

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
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (χ : DirichletCharacter ℂ N) : Lent χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · unfold Lent
    rw [if_pos h]
    exact LFunctionTrivChar₁_apply_one_ne_zero N
  · rw [Lent_of_ne h]
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by simp)
end PI.EF
