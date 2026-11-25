-- Prove2me | solution 1 for PI.WGL.EqvWt.sum_rowDeg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:02.041344+00:00
-- url     : https://prove2.me/submissions/89b788df-ce2b-44aa-b4fc-e4efe62a2937

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_PI_WGL_EqvWt_weight_colW_apply
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {r : ℕ} (lam : DomWeight r) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (hf : f ∈ nablaSq ℂ r lam) (m : Fin r × Fin r →₀ ℕ) (hm : coeff m f ≠ 0) :
    ∑ a, rowDeg m a = ∑ j, lam.natW j := by
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r r lam.natW := hf
  have hw : Finsupp.weight (colW r r) m = lam.natW :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hf').1 hm
  calc ∑ a, rowDeg m a = ∑ a, ∑ j, m (a, j) := rfl
    _ = ∑ j, ∑ a, m (a, j) := Finset.sum_comm
    _ = ∑ j, Finsupp.weight (colW r r) m j := by simp only [weight_colW_apply]
    _ = ∑ j, lam.natW j := by rw [hw]
end PI.WGL.EqvWt
