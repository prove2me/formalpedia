-- Prove2me | solution 1 for PI.OpWords.rop_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:47.708565+00:00
-- url     : https://prove2.me/submissions/e639add2-c42d-4bbc-9fe3-d8468164728e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Theorems.Thm_PI_OpWords_rop_apply

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
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution (a b : Fin k) (r : K) : Rop K k a b (C r) = 0 := by
  simp [rop_apply]
end PI.OpWords
