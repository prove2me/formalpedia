-- Prove2me | solution 1 for PI.OpWords.prodFact_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:44.099827+00:00
-- url     : https://prove2.me/submissions/21e86e18-4847-4b6c-ae44-5d9b60ef987a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Theorems.Thm_PI_OpWords_prodFact_fintype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] {k d : ℕ}
namespace PI.OpWords
theorem _root_.solution [CharZero K] (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) ≠ 0 := by
  rw [prodFact_fintype]
  exact Finset.prod_ne_zero_iff.2 (fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
end PI.OpWords
