-- Prove2me | solution 1 for PI.TOW.DegW.multideg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:09.371529+00:00
-- url     : https://prove2.me/submissions/a618c94f-d963-4fb4-acce-95d41e37233e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_MultidegSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.DegW
open PI.TO PI.TOW
variable {K : Type} [Field K] {n' k : ℕ}
namespace PI.TOW.DegW
theorem _root_.solution (a b : Fin n' × Fin k →₀ ℕ) (i : Fin n') :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]
end PI.TOW.DegW
