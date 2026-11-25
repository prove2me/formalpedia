-- Prove2me | solution 1 for PI.EF.cLine_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:07.975932+00:00
-- url     : https://prove2.me/submissions/b1d20110-1d9a-4a10-9ef2-9bf5f05cfc2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Theorems.Thm_PI_EF_log_ge_half

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
open Finset
namespace PI.EF
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : 0 < cLine u := by
  have hl := log_ge_half hu
  have h : 0 < 1 / Real.log u := one_div_pos.mpr (by linarith)
  unfold cLine
  linarith
end PI.EF
