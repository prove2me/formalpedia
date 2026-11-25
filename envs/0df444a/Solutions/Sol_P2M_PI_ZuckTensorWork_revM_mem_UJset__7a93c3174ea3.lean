-- Prove2me | solution 1 for P2M_PI_ZuckTensorWork_revM_mem_UJset__7a93c3174ea3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:37.157197+00:00
-- url     : https://prove2.me/submissions/96628f39-1309-41e1-9e05-e9f90c87545e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_mem_UJset_iff
import Theorems.Thm_PI_ZuckTensorWork_revE_revE


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
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) :
    revM g ∈ UJset (revE ε) := revM_mem_UJset_iff.mpr (by rwa [revE_revE])
end PI.ZuckTensorWork
