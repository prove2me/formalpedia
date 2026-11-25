-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.mem_UJset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:04.730426+00:00
-- url     : https://prove2.me/submissions/dfccf721-3639-4475-b7cc-f01fe5a710bd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_AdjointEquivalence

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ PI.UpqRep.UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl
end PI.UnitaryGroupMassFormula.DSIC
