-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.norm_matVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:17.744432+00:00
-- url     : https://prove2.me/submissions/fb8b4e9f-0690-4ad4-aba1-278300eccaff

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
theorem _root_.solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ‖matVec A‖ = hsN A := by
  rw [EuclideanSpace.norm_eq, hsN, Formalism.REAL.hs, Fintype.sum_prod_type]
  rfl
end PI.UnitaryGroupMassFormula.LCG
