-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.norm_add_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:08.177467+00:00
-- url     : https://prove2.me/submissions/9f890edf-3ca1-42bb-b673-34d5ee585148

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor
variable {p : ℕ} [Fact p.Prime]
namespace PI.CubicExponentialFactor.Wk
theorem _root_.solution {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
end PI.CubicExponentialFactor.Wk
