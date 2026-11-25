-- Prove2me | solution 1 for PI.WMI.MMap.evM_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:48.562868+00:00
-- url     : https://prove2.me/submissions/58b3c5fa-e209-483f-a346-c278918b42b0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_eval_aeval_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
namespace PI.WMI.MMap
theorem _root_.solution {N : ℕ} (t : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (aeval (fun v : Fin N × Fin N => C (t v.2) * X v) f) = evM (A * Matrix.diagonal t) f := by
  unfold evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  simp [Matrix.mul_diagonal, mul_comm]
end PI.WMI.MMap
