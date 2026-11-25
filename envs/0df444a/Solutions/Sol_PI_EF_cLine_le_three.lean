-- Prove2me | solution 1 for PI.EF.cLine_le_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:06.418549+00:00
-- url     : https://prove2.me/submissions/516b1b09-d75f-4ce3-a1e6-d0bce67f776a

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
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  have hl := log_ge_half hu
  have h : 1 / Real.log u ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  unfold cLine
  linarith
end PI.EF
