-- Prove2me | solution 1 for PI.ZuckTensorWork.revM_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:49.760712+00:00
-- url     : https://prove2.me/submissions/37b37717-6b12-48a2-9580-33563fb216dc

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
theorem _root_.solution (a b : Matrix (Fin n) (Fin n) ℂ) : revM (a * b) = revM a * revM b := by
  rw [revM_eq_submatrix, revM_eq_submatrix, revM_eq_submatrix, Matrix.submatrix_mul_equiv]
end PI.ZuckTensorWork
