-- Prove2me | solution 1 for PI.WMI.MMap.Fq_colAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:10.269288+00:00
-- url     : https://prove2.me/submissions/e03f06e5-456c-4890-a703-53c845da6686

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_evM_colAdd
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
theorem _root_.solution
    (hlow : ∀ a b : Fin N, a < b → ∀ (c : ℂ) (x : V), ⟪v0, P (1 + Matrix.single b a c) x⟫_ℂ = ⟪v0, x⟫_ℂ)
    (l j : Fin N) (hlj : l < j) (c : ℂ) (x : V) :
    colAdd ℂ (r := N) l j c (Fq hP v0 x) = Fq hP v0 x := poly_ext fun A => by
  rw [evM_colAdd, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, hP.mul, LinearMap.comp_apply, hlow l j hlj]
end PI.WMI.MMap
