-- Prove2me | solution 1 for PI.WGL.io_sqAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:46.318733+00:00
-- url     : https://prove2.me/submissions/05b4012c-b1a5-4997-be29-4fa10fa99053

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
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
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution {k : ℕ} (mu : DomWeight k) (g g' : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    sqAct ℂ k mu (g * g') f = sqAct ℂ k mu g (sqAct ℂ k mu g' f) := by
  have hrow : Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) ((g * g' : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ).transpose =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (g : Matrix (Fin k) (Fin k) ℂ).transpose).comp
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (g' : Matrix (Fin k) (Fin k) ℂ).transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.transpose_apply, Units.val_mul,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
    ring
  have hdet : detPow ℂ k (g * g') mu.detShift = detPow ℂ k g mu.detShift * detPow ℂ k g' mu.detShift := by
    unfold detPow
    rw [map_mul, mul_zpow, Units.val_mul]
  unfold sqAct
  rw [hrow, AlgHom.comp_apply, map_smul, smul_smul, hdet]
end PI.WGL
