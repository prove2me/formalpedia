-- Prove2me | solution 1 for PI.WMI.MMap.Fl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:53.918022+00:00
-- url     : https://prove2.me/submissions/e9e6d246-058a-4622-a0f5-919ef0dd4375

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap

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
theorem _root_.solution (x : V) : Fl hP v0 x = Fq hP v0 x := rfl
end PI.WMI.MMap
