-- Prove2me | solution 1 for PI.EF.Loc.locC_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.086999+00:00
-- url     : https://prove2.me/submissions/72292fe0-edab-4382-9f89-2e1159038f1a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology
namespace PI.EF.Loc
theorem _root_.solution {r R' R : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) : 0 < locC r R' R := by
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  have h1 : 0 < 4 * (r + R') / (R' - r) ^ 2 :=
    div_pos (by linarith) (pow_pos (by linarith) 2)
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have h2 : 0 < R' / (R * (R - R')) / Real.log (R / R') :=
    div_pos (div_pos hR' (mul_pos hR (by linarith))) hlog
  unfold locC
  linarith
end PI.EF.Loc
