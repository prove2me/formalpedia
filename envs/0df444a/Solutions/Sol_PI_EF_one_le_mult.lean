-- Prove2me | solution 1 for PI.EF.one_le_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:48.194475+00:00
-- url     : https://prove2.me/submissions/d81899d1-d777-43a1-ab23-5b2d123f5360

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_analyticAt_LFunction
import Theorems.Thm_PI_EF_analyticOrderAt_LFunction_ne_top

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
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s ≠ 1) (h0 : LFunction χ s = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) s := by
  have hne := analyticOrderAt_LFunction_ne_top χ hs
  have h0' : analyticOrderAt (LFunction χ) s ≠ 0 := by
    rw [Ne, (analyticAt_LFunction χ hs).analyticOrderAt_eq_zero]
    exact not_not.2 h0
  have hn : analyticOrderNatAt (LFunction χ) s ≠ 0 := by
    intro h
    apply h0'
    rw [← Nat.cast_analyticOrderNatAt hne, h]
    rfl
  omega
end PI.EF
