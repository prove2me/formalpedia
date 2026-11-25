-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.star_hs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:43.865048+00:00
-- url     : https://prove2.me/submissions/5fc05ddc-b588-4ebb-9894-41d841983a87

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hs k r i) = hs k r i := by
  simp only [hs]
  split_ifs <;> simp
end PI.QuotSetU.UnitaryGroupMassFormula
