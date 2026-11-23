-- Prove2me | solution 1 for PI.OpWords.pderiv_inl_tt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:24.172789+00:00
-- url     : https://prove2.me/submissions/3fb006bd-a3db-44d8-aab9-b0ef96d6db24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous

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
namespace PI.OpWords
theorem _root_.solution (K : Type) [Field K] (k : ℕ) (b : Fin k) :
    pderiv (Sum.inl b) (tt K k) = X (Sum.inr b) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]
end PI.OpWords
