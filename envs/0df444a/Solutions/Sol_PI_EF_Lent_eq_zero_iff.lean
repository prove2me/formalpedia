-- Prove2me | solution 1 for PI.EF.Lent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:20.579043+00:00
-- url     : https://prove2.me/submissions/497c3a09-cb65-448e-8b7d-faccc2b3eb5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_Lent_of_ne
import Theorems.Thm_PI_EF_Lent_one_apply

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
theorem _root_.solution (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  · rw [Lent_one_apply h hs, mul_eq_zero]
    simp [sub_eq_zero, hs]
  · rw [Lent_of_ne h]
end PI.EF
