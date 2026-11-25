-- Prove2me | solution 1 for PI.WGB.coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:33:03.098097+00:00
-- url     : https://prove2.me/submissions/4dad58f7-a569-4cfc-b8cd-58425d577f66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_aeval_scale_monomial
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
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (t : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (aeval (fun v : Fin n × Fin n => C (t v.2) * X v) P) = (m.prod fun v e => t v.2 ^ e) * coeff m P := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro m' a
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · intro p q hp hq
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end PI.WGB
