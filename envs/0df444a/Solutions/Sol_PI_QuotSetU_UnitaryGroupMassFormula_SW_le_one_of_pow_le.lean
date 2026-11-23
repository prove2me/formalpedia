-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.le_one_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:21.336092+00:00
-- url     : https://prove2.me/submissions/84114283-39e5-4983-b5c0-e693ce61892a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {x M : ℝ} (h : ∀ m : ℕ, x ^ m ≤ M) : x ≤ 1 := by
  by_contra hx
  push_neg at hx
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt M hx
  linarith [h m]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
