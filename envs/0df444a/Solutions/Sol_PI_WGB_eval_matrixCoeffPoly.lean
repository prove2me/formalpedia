-- Prove2me | solution 1 for PI.WGB.eval_matrixCoeffPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:37.408141+00:00
-- url     : https://prove2.me/submissions/1a843f89-de9e-44e8-acbf-60b4bbc7193f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_map_rowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_fockF_eq_sum
import Theorems.Thm_PI_WGB_iotaC_map
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
namespace PI.WGB
theorem _root_.solution (x : Fin n × Fin n → ℂ) : eval x (mcP f) = mcF f (matOf x) := by
  have hmap : map (eval x) (rowAct (MvPolynomial (Fin n × Fin n) ℂ) (iotaC _ n k (genY n)).transpose
      (map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) f)) = rowAct ℂ (iotaC ℂ n k (matOf x)).transpose f := by
    rw [map_rowAct, map_map, Matrix.transpose_map, iotaC_map]
    have h1 : (eval x).comp (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = RingHom.id ℂ :=
      RingHom.ext fun a => by simp
    have h2 : (genY n).map (eval x) = matOf x := by ext i j; simp [genY, matOf]
    rw [h1, map_id, h2]
  unfold mcP mcF
  rw [map_sum, fockF_eq_sum _ f f.support (fun m _ h => mem_support_iff.mpr h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, ← coeff_map, hmap, mul_assoc]
end PI.WGB
