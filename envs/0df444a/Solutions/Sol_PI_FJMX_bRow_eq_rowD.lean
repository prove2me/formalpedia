-- Prove2me | solution 1 for PI.FJMX.bRow_eq_rowD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:02.814883+00:00
-- url     : https://prove2.me/submissions/f32b1450-6131-4591-ac68-ae9a5aeda5f7

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
theorem _root_.solution (ι : Fin m × Fin n → σ) (a b : Fin m) (f : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b f = rowD ι a b f := by
  rw [PI.FJM.bRow, rowD, derSum_apply, LinearMap.sum_apply]
  rfl
end PI.FJMX
