-- Prove2me | solution 1 for PI.EF.four_mul_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:09.85948+00:00
-- url     : https://prove2.me/submissions/3c9a7fcc-cec3-4875-acc4-20ed90b537d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight

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
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : 4 * x ≤ x ^ 3 := by
  have h4 : 4 ≤ x ^ 2 := by nlinarith
  nlinarith
end PI.EF
