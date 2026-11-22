-- Prove2me | solution 1 for PI.OpWords.rop_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:39.576265+00:00
-- url     : https://prove2.me/submissions/3bbd75b9-632f-4305-b050-28949deb1ef6

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
theorem _root_.solution (K : Type) [Field K] (k : ℕ) (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl
end PI.OpWords
