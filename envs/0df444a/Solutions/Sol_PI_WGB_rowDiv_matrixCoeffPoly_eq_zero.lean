-- Prove2me | solution 1 for PI.WGB.rowDiv_matrixCoeffPoly_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:29.957401+00:00
-- url     : https://prove2.me/submissions/7acf25c9-5886-4b39-bf72-73cf55af7b46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_matOf_self
import Theorems.Thm_PI_WGB_eval_aeval_self
import Theorems.Thm_PI_WGB_eval_matrixCoeffPoly
import Theorems.Thm_PI_WGB_mcF_Lmul
import Theorems.Thm_PI_WGB_isUU_E_conj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_wlocal_eval_rowGen
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
    (a b : Fin n) (hab : a < b) (kk : ℕ) (hk : 1 ≤ kk) : rowDiv ℂ a b kk (mcP f) = 0 := by
  have hpt : ∀ c : ℂ, rowAct ℂ (Formalism.UG.P.wlocal_E b a c) (mcP f) = mcP f := by
    intro c
    apply MvPolynomial.funext
    intro x
    rw [rowAct, eval_aeval_self]
    have key : (fun v : Fin n × Fin n => eval x (∑ b' : Fin n, C (Formalism.UG.P.wlocal_E b a c v.1 b') * X (b', v.2))) =
        fun v => (Formalism.UG.P.wlocal_E b a c * matOf x) v.1 v.2 := by
      funext v
      simp [matOf, Matrix.mul_apply]
    rw [key, eval_matrixCoeffPoly, matOf_self, mcF_Lmul hU _ _ (isUU_E_conj a b hab c), ← eval_matrixCoeffPoly]
  set q := rowGen ℂ a b (mcP f) - Polynomial.C (mcP f) with hq
  have hroot : ∀ c : ℂ, q.IsRoot (C c) := by
    intro c
    rw [Polynomial.IsRoot, hq, Polynomial.eval_sub, Formalism.UG.P.wlocal_eval_rowGen b a c (mcP f), hpt,
      Polynomial.eval_C, sub_self]
  have hq0 : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q
    (Set.infinite_of_injective_forall_mem (MvPolynomial.C_injective (Fin n × Fin n) ℂ) hroot)
  have : rowGen ℂ a b (mcP f) = Polynomial.C (mcP f) := sub_eq_zero.mp hq0
  rw [rowDiv, this, Polynomial.coeff_C, if_neg (by omega)]
end PI.WGB
