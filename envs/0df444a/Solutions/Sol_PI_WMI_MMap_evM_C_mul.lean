-- Prove2me | solution 1 for PI.WMI.MMap.evM_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:33.377012+00:00
-- url     : https://prove2.me/submissions/4217d439-7138-4035-8b0a-aaedf5b0df77

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
namespace PI.WMI.MMap
theorem _root_.solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (C c * p) = c * evM A p := by
  rw [evM, evM, eval_mul, eval_C]
end PI.WMI.MMap
