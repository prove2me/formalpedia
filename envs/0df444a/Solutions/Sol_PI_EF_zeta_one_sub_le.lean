-- Prove2me | solution 1 for PI.EF.zeta_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:16:00.747001+00:00
-- url     : https://prove2.me/submissions/f435e13d-1617-4d43-8e97-40032d528f2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthZeta
import Theorems.Thm_PI_EF_norm_L_one_sub_le


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
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 6 * ‖w + 1‖ ^ 5 * ‖riemannZeta w‖ := by
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have h0 := norm_L_one_sub_le (N := 1) hp h1 h2 (Or.inr h)
  simpa [DirichletCharacter.LFunction_modOne_eq] using h0
end PI.EF
