-- Prove2me | solution 1 for PI.WGB.colAdd_matrixCoeffPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:59.241704+00:00
-- url     : https://prove2.me/submissions/6bee13ae-8007-4b1f-9de3-f373c8d3eae3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_matOf_self
import Theorems.Thm_PI_WGB_eval_aeval_self
import Theorems.Thm_PI_WGB_eval_matrixCoeffPoly
import Theorems.Thm_PI_WGB_mcF_mulU
import Theorems.Thm_PI_WGB_isUU_E
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
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (l j : Fin n) (hlj : l < j) (c : ℂ) : colAdd ℂ l j c (mcP f) = mcP f := by
  apply MvPolynomial.funext
  intro x
  rw [colAdd, eval_aeval_self]
  have key : (fun v : Fin n × Fin n => eval x (if v.2 = j then X v + C c * X (v.1, l) else X v)) =
      fun v => (matOf x * Formalism.UG.P.wlocal_E l j c) v.1 v.2 := by
    funext v
    simp only [matOf, Matrix.mul_apply, Matrix.of_apply, Formalism.UG.P.wlocal_E, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : v.2 = j
    · simp [h, mul_comm] <;> rw [← h]
    · simp [h]
  rw [key, eval_matrixCoeffPoly, matOf_self, mcF_mulU hU _ _ (isUU_E l j hlj c), ← eval_matrixCoeffPoly]
end PI.WGB
