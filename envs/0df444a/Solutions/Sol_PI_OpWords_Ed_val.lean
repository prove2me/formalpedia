-- Prove2me | solution 1 for PI.OpWords.Ed_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:22.700611+00:00
-- url     : https://prove2.me/submissions/e13723a7-7d1b-43bf-a2bc-939301c4ca85

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
theorem _root_.solution (a b : Fin k) (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    (Formalism.MainNotions.TestSideCounting.Ed K k d a b F : MvPolynomial (Fin k) K) = X a * pderiv b (F : MvPolynomial (Fin k) K) :=
  rfl
end PI.OpWords
