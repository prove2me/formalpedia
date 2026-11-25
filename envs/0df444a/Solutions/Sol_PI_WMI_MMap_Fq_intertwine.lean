-- Prove2me | solution 1 for PI.WMI.MMap.Fq_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:14.735744+00:00
-- url     : https://prove2.me/submissions/707417aa-cf0f-402e-bf0d-73ecf54ec7b9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_evM_rowAct
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
theorem _root_.solution (g : Matrix (Fin N) (Fin N) ℂ) (x : V) :
    Fq hP v0 (P g x) = rowAct ℂ (n := N) gᵀ (Fq hP v0 x) := poly_ext fun A => by
  rw [evM_rowAct, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.transpose_transpose, hP.mul,
    LinearMap.comp_apply]
end PI.WMI.MMap
