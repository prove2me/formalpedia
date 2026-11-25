-- Prove2me | solution 1 for PI.TOW.fockR_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:09.009901+00:00
-- url     : https://prove2.me/submissions/71e32562-b113-4e11-affd-06aef9270d79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin

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
open PI PI.TOW
open PI.TO
variable {σ R : Type*} [CommRing R]
namespace PI.TOW
theorem _root_.solution (f : MvPolynomial σ R) : fockR f 0 = 0 := by
  simp [fockR]
end PI.TOW
