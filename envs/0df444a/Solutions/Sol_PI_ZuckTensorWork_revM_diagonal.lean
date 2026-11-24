-- Prove2me | solution 1 for PI.ZuckTensorWork.revM_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:58.04553+00:00
-- url     : https://prove2.me/submissions/1086d951-c957-405b-8657-e831f168f57b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_eq_submatrix

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
theorem _root_.solution (d : Fin n → ℂ) : revM (diagonal d) = diagonal (d ∘ Fin.rev) := by
  rw [revM_eq_submatrix, Matrix.submatrix_diagonal_equiv]
  congr 1
end PI.ZuckTensorWork
