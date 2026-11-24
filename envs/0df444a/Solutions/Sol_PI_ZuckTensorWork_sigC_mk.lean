-- Prove2me | solution 1 for PI.ZuckTensorWork.sigC_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:12.64379+00:00
-- url     : https://prove2.me/submissions/6f889114-4bcc-4811-b207-4fac8746b50f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (x : H) :
    sigC σ g (Cj.mk x) = Cj.mk (σ (revM g) x) := rfl
end PI.ZuckTensorWork
