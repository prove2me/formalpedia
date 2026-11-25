-- Prove2me | solution 1 for PI.OpWords.weight_wxi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:10.311102+00:00
-- url     : https://prove2.me/submissions/c0e79bf3-2137-479b-8d3b-6ab543f766c0

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
theorem _root_.solution (m g : Fin k →₀ ℕ) : Finsupp.weight (wxi k) (Finsupp.sumElim m g) = g.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type, Finsupp.degree_eq_sum]
end PI.OpWords
