-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.tt_homog_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:57.825075+00:00
-- url     : https://prove2.me/submissions/c8e75ed2-4d65-4846-a2b3-72b1fd38b080

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution : IsWeightedHomogeneous (wxi k) (tt K k) 1 := by
  show IsWeightedHomogeneous (wxi k) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 1
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (wxi k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (wxi k) (Sum.inr i))
  simpa [wxi] using h
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
