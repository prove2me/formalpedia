-- Prove2me | solution 1 for PI.OpWords.pderiv_inl_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:18.291796+00:00
-- url     : https://prove2.me/submissions/0d79c9b5-a016-4822-bc69-be66452e0a4e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff

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
theorem _root_.solution (b : Fin k) (g : Fin k →₀ ℕ) :
    pderiv (Sum.inl b) (monomial (g.mapDomain Sum.inr) (1 : K) : Pol K k) = 0 := by
  simp [pderiv_monomial, Finsupp.mapDomain_notin_range]
end PI.OpWords
