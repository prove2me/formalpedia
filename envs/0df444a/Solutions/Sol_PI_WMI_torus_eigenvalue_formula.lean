-- Prove2me | solution 1 for PI.WMI.torus_eigenvalue_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:57.966831+00:00
-- url     : https://prove2.me/submissions/4521e55e-4541-439f-9ce0-aea7e9d294e5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_TorusEigenvalueFormula
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WMI_lowerInv_adj
import Theorems.Thm_PI_WMI_lowerInv_torus_mem
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
namespace PI.WMI
theorem _root_.solution : TorusEig := by
  intro N Λ H _ _ σ S K P hU hstab hPσ v0 hw θ x
  have hwt : σ (torus (-θ)) (v0 : H) =
      Complex.exp (((∑ a, Λ a * (-θ) a : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
    hw (-θ) (lowerInv_torus_mem (-θ))
  have hdet : (torus θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
    rw [torus, Matrix.det_diagonal]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [Submodule.coe_inner, hPσ (torus θ) (lowerInv_torus_mem θ) x, inner_smul_right,
    lowerInv_adj hU θ, hwt, inner_smul_left, ← Submodule.coe_inner, hdet, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  ring_nf
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring
end PI.WMI
