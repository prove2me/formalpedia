-- Prove2me | solution 1 for PI.WSF.cr_rowAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:03.33571+00:00
-- url     : https://prove2.me/submissions/5392128c-2bf2-4732-82d9-ae1afa02abfe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Theorems.Thm_PI_WSF_cr_rowAct_X
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
theorem _root_.solution {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) s = s := by
  have h : (Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) :
      MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [cr_rowAct_X]
    simp [Matrix.one_apply]
  rw [h]
  rfl
end PI.WSF
