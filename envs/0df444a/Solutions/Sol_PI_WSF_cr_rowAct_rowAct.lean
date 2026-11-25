-- Prove2me | solution 1 for PI.WSF.cr_rowAct_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:07.105544+00:00
-- url     : https://prove2.me/submissions/9110ba98-974b-414f-add5-8572f3a04575

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Theorems.Thm_PI_WSF_cr_rowAct_X
import Theorems.Thm_PI_WSF_cr_rowAct_C
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
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial
namespace PI.WSF
theorem _root_.solution {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h s) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) s := by
  have hc : (Formalism.GradedWeylDivisibility.rowAct ℂ g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [AlgHom.comp_apply, cr_rowAct_X, map_sum, cr_rowAct_X]
    simp only [map_mul, cr_rowAct_C, cr_rowAct_X, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm
  rw [← hc, AlgHom.comp_apply]
end PI.WSF
