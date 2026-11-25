-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.jm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:01.541864+00:00
-- url     : https://prove2.me/submissions/b6646c24-cb22-4208-bd3d-4ab09dc17036

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (jm_sq ε)
end PI.UnitaryGroupMassFormula.DSIC
