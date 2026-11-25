-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.jm_jm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:05.991033+00:00
-- url     : https://prove2.me/submissions/bf7445d4-c7c5-4e7a-8c71-5895ce3fa513

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_AdjointEquivalence
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_jm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open PI.DSInfCharCap
open scoped InnerProductSpace Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, jm_sq, Matrix.one_mul]
end PI.UnitaryGroupMassFormula.DSIC
