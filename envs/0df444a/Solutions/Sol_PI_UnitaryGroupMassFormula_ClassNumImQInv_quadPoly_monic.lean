-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.quadPoly_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:35.566614+00:00
-- url     : https://prove2.me/submissions/04a47d61-e539-4944-9877-63f58c1da845

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInv
open PI.ClassNumImQ
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
namespace PI.UnitaryGroupMassFormula.ClassNumImQInv
theorem _root_.solution (d : ℕ) : (quadPoly d).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero
end PI.UnitaryGroupMassFormula.ClassNumImQInv
