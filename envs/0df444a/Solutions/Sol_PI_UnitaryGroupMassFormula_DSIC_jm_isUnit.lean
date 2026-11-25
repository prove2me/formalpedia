-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.jm_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:05.333325+00:00
-- url     : https://prove2.me/submissions/86c56cd9-ea29-49ba-a580-0c2302aab2e1

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, jm_sq ε, jm_sq ε⟩, rfl⟩
end PI.UnitaryGroupMassFormula.DSIC
