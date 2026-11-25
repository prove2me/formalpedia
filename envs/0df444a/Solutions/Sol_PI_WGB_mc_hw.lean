-- Prove2me | solution 1 for PI.WGB.mc_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:00.094303+00:00
-- url     : https://prove2.me/submissions/e0c3b9f7-0077-43ce-ae98-86c72d4c92dd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_matOf_self
import Theorems.Thm_PI_WGB_eval_aeval_self
import Theorems.Thm_PI_WGB_eval_matrixCoeffPoly
import Theorems.Thm_PI_WGB_mcF_diag
import Theorems.Thm_PI_WGB_mcF_one
import Theorems.Thm_PI_WGB_colAdd_matrixCoeffPoly
import Theorems.Thm_PI_WGB_rowDiv_matrixCoeffPoly_eq_zero
import Theorems.Thm_PI_WGB_isWH_of_scale
import Theorems.Thm_PI_WGB_hwAt_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylPoint
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine
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
theorem _root_.solution (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (Y : Matrix (Fin n) (Fin n) ℂ) : mcF f Y = fockF f f * hwAt κ Y := by
  have hhom : IsWeightedHomogeneous (colW n n) (mcP f) κ := by
    apply isWH_of_scale
    intro t
    apply MvPolynomial.funext
    intro x
    rw [eval_aeval_self, eval_mul, eval_C, eval_matrixCoeffPoly, eval_matrixCoeffPoly]
    have : matOf (fun v : Fin n × Fin n => eval x (C ((t v.2 : ℂ)) * X v)) =
        matOf x * Matrix.diagonal fun i => (t i : ℂ) := by
      ext i j; simp [matOf, Matrix.mul_diagonal, mul_comm]
    rw [this, mcF_diag hT]
  have hmem : mcP f ∈ dualWeyl ℂ n n κ :=
    (dualWeylPoint ℂ n n κ (mcP f)).mpr ⟨hhom, fun l j hlj c => colAdd_matrixCoeffPoly hU l j hlj c⟩
  obtain ⟨c, hc⟩ := hwLine ℂ n n le_rfl κ hκ (mcP f) hmem
    (fun a b hab kk hk => rowDiv_matrixCoeffPoly_eq_zero hU a b hab kk hk)
  have h1 : eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (mcP f) = fockF f f := by
    rw [eval_matrixCoeffPoly, matOf_self, mcF_one]
  rw [hc, smul_eval] at h1
  have h1' : c = fockF f f := by
    have := hwAt_one κ
    unfold hwAt at this
    rw [this, mul_one] at h1
    exact h1
  rw [← matOf_self Y, ← eval_matrixCoeffPoly, hc, smul_eval, h1']
  rfl
end PI.WGB
