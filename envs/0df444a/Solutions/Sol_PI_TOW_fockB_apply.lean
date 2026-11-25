-- Prove2me | solution 1 for PI.TOW.fockB_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:05.11105+00:00
-- url     : https://prove2.me/submissions/ede562e7-8e4b-45be-99dd-007df7d4de61

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
theorem _root_.solution (f g : MvPolynomial σ R) : fockB σ R f g = fockR f g := rfl
end PI.TOW
