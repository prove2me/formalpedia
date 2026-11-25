-- Prove2me | solution 1 for PI.EF.rpow_cLine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:03.685343+00:00
-- url     : https://prove2.me/submissions/123864af-ba91-4866-8fb3-97e9349ef02c

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
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u = Real.exp 1 * u := by
  have hu0 : 0 < u := by linarith
  have hl : Real.log u ≠ 0 := by linarith [log_ge_half hu]
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl, mul_comm]
end PI.EF
