-- Prove2me | solution 1 for PI.WMI.MMap.Fq_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:26.162259+00:00
-- url     : https://prove2.me/submissions/4569dede-bab6-4d8d-9e53-a916bf24cf47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_coeff_scale
import Theorems.Thm_PI_WMI_MMap_prod_exp
import Theorems.Thm_PI_WMI_MMap_real_eq_of_exp
import Theorems.Thm_PI_WMI_MMap_Fq_scale
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
variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)} (hP : IsPolyMon P) (v0 : V)
namespace PI.WMI.MMap
theorem _root_.solution (μ : Fin N → ℤ) (K : ℕ)
    (htor : ∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ)
    (x : V) (m : Fin N × Fin N →₀ ℕ) (hm : coeff m (Fq hP v0 x) ≠ 0) (s : Fin N) :
    (((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ)) : ℤ) = μ s + K := by
  have key : ((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ) : ℝ) = (μ s : ℝ) + K := by
    apply real_eq_of_exp
    intro τ
    have h1 := congrArg (coeff m) (Fq_scale hP v0 μ K htor (fun s' => if s' = s then τ else 0) x)
    rw [coeff_scale, coeff_C_mul, mul_comm (Complex.exp _), prod_exp m (fun s' => if s' = s then τ else 0)] at h1
    have h2 := mul_left_cancel₀ hm h1
    have e1 : (∑ v : Fin N × Fin N, (m v : ℝ) * (if v.2 = s then τ else 0)) =
        τ * ((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    have e2 : (∑ a : Fin N, ((μ a : ℝ) + K) * (if a = s then τ else 0)) = τ * ((μ s : ℝ) + K) := by
      simp [mul_ite, Finset.sum_ite_eq']
      ring
    rw [e1, e2] at h2
    exact h2
  exact_mod_cast key
end PI.WMI.MMap
