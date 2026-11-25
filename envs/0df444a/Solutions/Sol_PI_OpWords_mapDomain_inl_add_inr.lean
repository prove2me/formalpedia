-- Prove2me | solution 1 for PI.OpWords.mapDomain_inl_add_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:05.434799+00:00
-- url     : https://prove2.me/submissions/d3476208-f348-4c13-982e-10fe83003797

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
theorem _root_.solution (u g : Fin k →₀ ℕ) :
    u.mapDomain Sum.inl + g.mapDomain Sum.inr = Finsupp.sumElim u g := by
  ext v
  rcases v with i | i
  · simp [Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_notin_range]
  · simp [Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_notin_range]
end PI.OpWords
