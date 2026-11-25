-- Prove2me | solution 1 for PI.OpWords.mem_antidiag_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:09.936374+00:00
-- url     : https://prove2.me/submissions/7ba976c2-3949-47d1-ad23-24260a13e597

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
theorem _root_.solution (g : Fin k →₀ ℕ) :
    g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d ↔ g.degree = d := by
  rw [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp
end PI.OpWords
