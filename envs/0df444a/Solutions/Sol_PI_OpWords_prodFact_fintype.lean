-- Prove2me | solution 1 for PI.OpWords.prodFact_fintype
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:29.518598+00:00
-- url     : https://prove2.me/submissions/7c7efc0d-eae7-4c72-bf68-684ffcc00495

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
    g.prod (fun _ n => (n.factorial : K)) = ∏ i, ((g i).factorial : K) := by
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)
end PI.OpWords
