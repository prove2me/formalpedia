-- Prove2me | solution 1 for PI.WMI.MMap.Fq_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:05.481+00:00
-- url     : https://prove2.me/submissions/71a06481-8ea5-4a25-8009-242fac3b43d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_evM_C_mul
import Theorems.Thm_PI_WMI_MMap_evM_scale
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (θ : Fin N → ℝ) (x : V) :
    aeval (fun v : Fin N × Fin N => C (Complex.exp ((θ v.2 : ℂ) * Complex.I)) * X v) (Fq hP v0 x) =
      C (Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I)) * Fq hP v0 x :=
  poly_ext fun A => by
    rw [evM_scale (fun s => Complex.exp ((θ s : ℂ) * Complex.I)), evM_C_mul, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.diagonal_transpose, ← htor θ,
      hP.mul, LinearMap.comp_apply]
    rfl
end PI.WMI.MMap
