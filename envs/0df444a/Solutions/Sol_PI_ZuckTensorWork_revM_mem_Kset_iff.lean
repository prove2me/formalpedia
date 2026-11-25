-- Prove2me | solution 1 for PI.ZuckTensorWork.revM_mem_Kset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:35.165748+00:00
-- url     : https://prove2.me/submissions/92ce85af-9c44-4780-a47b-5cb42d9ff1e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_inj
import Theorems.Thm_PI_ZuckTensorWork_revM_mul
import Theorems.Thm_PI_ZuckTensorWork_revM_eq_one_iff
import Theorems.Thm_PI_ZuckTensorWork_revM_conjTranspose
import Theorems.Thm_PI_ZuckTensorWork_Jm_eq_revM

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
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} :
    revM g ∈ Kset ε ↔ g ∈ Kset (revE ε) := by
  show (revM g ∈ unitaryGroup (Fin n) ℂ ∧ revM g * Jm ε = Jm ε * revM g) ↔
    (g ∈ unitaryGroup (Fin n) ℂ ∧ g * Jm (revE ε) = Jm (revE ε) * g)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, revM_conjTranspose, ← revM_mul, revM_eq_one_iff, Jm_eq_revM ε,
    ← revM_mul, ← revM_mul, revM_inj]
end PI.ZuckTensorWork
