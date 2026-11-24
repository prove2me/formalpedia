-- Prove2me | solution 1 for PI.ScRefExists.WB.mem_WA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:56:30.357097+00:00
-- url     : https://prove2.me/submissions/aa4bc723-6ed3-4694-871b-4be541564cb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WB
theorem _root_.solution {p r : ℕ} {e f : Fin r → Fin I.n → I.E} {x : Fin I.n → I.E} :
    x ∈ WA I p r e f ↔ x ∈ LA I p ∧ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0 := Iff.rfl
end PI.ScRefExists.WB
