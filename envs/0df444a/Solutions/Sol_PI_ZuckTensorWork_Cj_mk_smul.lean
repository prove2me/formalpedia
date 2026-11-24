-- Prove2me | solution 1 for PI.ZuckTensorWork.Cj.mk_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:09.618455+00:00
-- url     : https://prove2.me/submissions/c84ef2fc-5f90-4efb-b991-929eaa8ae37d

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
namespace PI.ZuckTensorWork
namespace Cj
theorem _root_.solution (c : ℂ) (x : H) : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
  show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
  rw [Complex.conj_conj]
end Cj
end PI.ZuckTensorWork
