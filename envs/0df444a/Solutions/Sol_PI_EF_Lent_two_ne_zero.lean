-- Prove2me | solution 1 for PI.EF.Lent_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:11.503106+00:00
-- url     : https://prove2.me/submissions/81fa6420-3c40-4e0e-b7e3-687e1165e1e1

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
theorem _root_.solution (χ : DirichletCharacter ℂ N) : Lent χ 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have hL : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (by norm_num)
  by_cases h : χ = 1
  · rw [Lent_one_apply h h2]
    exact mul_ne_zero (sub_ne_zero.mpr h2) hL
  · rw [Lent_of_ne h]
    exact hL
end PI.EF
