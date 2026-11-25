-- Prove2me | solution 1 for PI.EF.perron_gluing_sides
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:26.532327+00:00
-- url     : https://prove2.me/submissions/40c0e8e2-8b47-4a7b-81c9-c1211ee77fdf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronLOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronGlue
import Theorems.Thm_PI_EF_PK_sidesBound_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF
namespace PI.EF
theorem _root_.solution : GlueSides := by
  rintro κ _ ⟨C1, hC1, hH⟩ ⟨C2, hC2, hL⟩
  exact ⟨21 * C1 + 8 * C2, by positivity, PK.sidesBound_of hC1.le hC2.le hH hL⟩
end PI.EF
