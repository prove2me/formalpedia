-- Prove2me | solution 1 for PI.WMI.MMap.aeval_scale_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:29.396878+00:00
-- url     : https://prove2.me/submissions/8843c8be-2ff7-49c6-85e7-18ef7c120588

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (u : σ →₀ ℕ) (c : ℂ) :
    aeval (fun v : σ => C (w v) * X v) (monomial u c) = monomial u (c * ∏ v, w v ^ u v) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (w v) : MvPolynomial σ ℂ) ^ e) = C (u.prod fun v e => w v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), monomial_eq, C_mul, algebraMap_eq]
  ring
end PI.WMI.MMap
