-- Prove2me | solution 1 for PI.ZuckTensorWork.vector_norm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:42.188288+00:00
-- url     : https://prove2.me/submissions/65f648fd-dd98-453f-bec0-947d86751665

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_RevNum
import Theorems.Thm_PI_ZuckTensorWork_revNum_rhoC
import Theorems.Thm_PI_ZuckTensorWork_revNum_nsq
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
theorem _root_.solution : VNormRev := by
  intro n ε ν
  have e : revP ν + (2 : ℝ) • rhoC (revE ε) = revP (ν + (2 : ℝ) • rhoC ε) := by
    funext a
    simp only [revP, Pi.add_apply, Pi.smul_apply, smul_eq_mul, revNum_rhoC]
    ring
  simp only [vNormSq]
  rw [e, revNum_nsq]
end PI.ZuckTensorWork
