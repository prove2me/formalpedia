-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.pow_bdd_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:41:17.303005+00:00
-- url     : https://prove2.me/submissions/469f4af7-314e-4f75-9e70-482188fd9c7e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution {x M : ℝ} (hx : 0 < x) (h : ∀ n : ℕ, x ^ n ≤ M) : x ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  exact absurd (h n) (not_le.2 hn)
end PI.QuotSetU.UnitaryGroupMassFormula
