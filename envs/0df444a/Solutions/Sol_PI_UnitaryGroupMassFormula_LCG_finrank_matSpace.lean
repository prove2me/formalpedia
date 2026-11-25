-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.finrank_matSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:05.133576+00:00
-- url     : https://prove2.me/submissions/8533bac2-8120-414f-ab81-f926459394c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_PackLem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (N : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin N × Fin N)) = 2 * N ^ 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, sq]
end PI.UnitaryGroupMassFormula.LCG
