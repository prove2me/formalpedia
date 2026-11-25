-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_hs_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:39.292+00:00
-- url     : https://prove2.me/submissions/1b100e74-93ad-4f2e-8842-96e9b835e261

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsN A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold hsN Formalism.REAL.hs
  rw [Real.sq_sqrt (by positivity)]
end PI.UnitaryGroupMassFormula.LCG
