-- Prove2me | solution 1 for PI.ZuckTensorWork.revNum_nsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:19:18.901036+00:00
-- url     : https://prove2.me/submissions/b663b9b8-3f63-4ce0-952d-14440adab8f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_RevNum
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.ZuckTensorWork.Cj.mk_un
attribute [local simp] PI.ZuckTensorWork.Cj.un_mk



set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution (u : Fin n → ℝ) : nsq (revP u) = nsq u := by
  simp only [nsq, dot, revP, neg_mul_neg]
  exact Equiv.sum_comp Fin.revPerm (fun a => u a * u a)
end PI.ZuckTensorWork
