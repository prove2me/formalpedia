-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.BoxB.norm_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:45.882369+00:00
-- url     : https://prove2.me/submissions/71aa6e2e-c355-4abd-85fa-148918dd9270

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_frob_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_hs_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.BoxB
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace
namespace PI.UnitaryGroupMassFormula.LCG.BoxB
theorem _root_.solution : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [frob_eq, hs_one]
end PI.UnitaryGroupMassFormula.LCG.BoxB
