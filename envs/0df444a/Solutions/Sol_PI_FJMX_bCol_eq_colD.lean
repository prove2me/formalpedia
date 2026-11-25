-- Prove2me | solution 1 for PI.FJMX.bCol_eq_colD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:59.740769+00:00
-- url     : https://prove2.me/submissions/5e8746fd-74df-4e79-824c-c013986efb1d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_derSum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m n : ℕ}
namespace PI.FJMX
theorem _root_.solution (ι : Fin m × Fin n → σ) (c d : Fin n) (f : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d f = colD ι c d f := by
  rw [PI.FJM.bCol, colD, derSum_apply, LinearMap.sum_apply]
  rfl
end PI.FJMX
