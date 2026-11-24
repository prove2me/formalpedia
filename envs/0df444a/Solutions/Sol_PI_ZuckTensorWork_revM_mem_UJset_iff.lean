-- Prove2me | solution 1 for PI.ZuckTensorWork.revM_mem_UJset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:42.271775+00:00
-- url     : https://prove2.me/submissions/1e5ad3b2-6325-4cf0-bdc8-2fe2cdaaa8db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_inj
import Theorems.Thm_PI_ZuckTensorWork_revM_mul
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
    revM g ∈ UJset ε ↔ g ∈ UJset (revE ε) := by
  show inUJ ε (revM g) ↔ inUJ (revE ε) g
  unfold inUJ
  rw [Jm_eq_revM ε, revM_conjTranspose, ← revM_mul, ← revM_mul, revM_inj]
end PI.ZuckTensorWork
