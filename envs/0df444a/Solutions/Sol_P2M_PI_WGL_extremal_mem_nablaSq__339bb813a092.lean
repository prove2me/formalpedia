-- Prove2me | solution 1 for P2M_PI_WGL_extremal_mem_nablaSq__339bb813a092
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:18.908058+00:00
-- url     : https://prove2.me/submissions/2fa4c6c0-2cc4-4ddc-be18-f4dca30841ec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDecomp
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))
end PI.WGL
