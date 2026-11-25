-- Prove2me | solution 1 for PI.Dv.ProjAW.one_sub_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:29.296389+00:00
-- url     : https://prove2.me/submissions/5e2bc6e6-ac0c-4287-9cf5-35da09366cda

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution {f : Module.End K A.V} (hf : f * f = f) : (1 - f) * (1 - f) = 1 - f := by
  rw [mul_sub, mul_one, sub_mul, one_mul, hf, sub_self, sub_zero]
end PI.Dv.ProjAW
