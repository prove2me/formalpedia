-- Prove2me | solution 1 for PI.EF.log_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:33.318737+00:00
-- url     : https://prove2.me/submissions/bd4cc9c5-e2c8-440d-b060-0863387300c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum

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
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h2 := Real.log_le_log (by norm_num) hu
  have h3 := Real.log_two_gt_d9
  linarith
end PI.EF
