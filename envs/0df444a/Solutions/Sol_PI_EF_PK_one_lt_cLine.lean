-- Prove2me | solution 1 for PI.EF.PK.one_lt_cLine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:13.099264+00:00
-- url     : https://prove2.me/submissions/14653c73-8c57-4c89-9aaa-8eef2163f68b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries
namespace PI.EF.PK
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : 1 < cLine u := by
  have h := Real.log_pos (by linarith : (1:ℝ) < u)
  have h2 := one_div_pos.mpr h
  show 1 < 1 + 1 / Real.log u
  linarith
end PI.EF.PK
