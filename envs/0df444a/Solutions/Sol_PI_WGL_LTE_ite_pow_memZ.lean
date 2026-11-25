-- Prove2me | solution 1 for PI.WGL.LTE.ite_pow_memZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:36.171802+00:00
-- url     : https://prove2.me/submissions/dc480043-c03a-403f-8208-f7f3107724c5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Theorems.Thm_PI_WGL_LTE_pow_memZ
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


section
noncomputable section
namespace PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
private theorem one_mem_dualWeyl_int {N : ℕ} : (1 : MvPolynomial (Fin N × Fin N) ℤ) ∈ dualWeyl ℤ N N 0 := by
  unfold dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one ℤ _
  · simp [Submodule.mem_iInf, LinearMap.mem_ker]
end PI.WGL.LTE
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {N s : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N (initW N s)) (e : ℕ) :
    (if c then f ^ e else 1) ∈ dualWeyl ℤ N N ((if c then e else 0) • initW N s) := by
  split_ifs
  · exact pow_memZ _ f hf e
  · simpa using (one_mem_dualWeyl_int (N := N))
end PI.WGL.LTE
