-- Prove2me | solution 1 for PI.OpWords.tt_va
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:14.376182+00:00
-- url     : https://prove2.me/submissions/74bbb135-baf9-41a7-ab69-a89b6b035af2

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
theorem _root_.solution (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    IsWeightedHomogeneous (va k a) (tt K k) 0 := by
  show IsWeightedHomogeneous (va k a) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 0
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (va k a) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (va k a) (Sum.inr i))
  by_cases hi : i = a <;> simpa [va, hi] using h
end PI.OpWords
