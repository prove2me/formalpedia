-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.theta_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:39.852924+00:00
-- url     : https://prove2.me/submissions/64123c65-5060-4b3f-a1da-43450864174d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (b : ℤ) (d : ℕ) : UnitDetRootDefs.cmTheta b d ∈ KF b d :=
    IntermediateField.mem_adjoin_simple_self ℚ (UnitDetRootDefs.cmTheta b d)
end PI.UnitaryGroupMassFormula.UnitDetRoot
