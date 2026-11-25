-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.isWeightedHomogeneous_pairing_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:43.013464+00:00
-- url     : https://prove2.me/submissions/f1897d76-1091-4ea0-a2e2-43ecfb7b45a8

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
theorem _root_.solution : IsWeightedHomogeneous (wx k) (tt K k) 1 := by
  show IsWeightedHomogeneous (wx k) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 1
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (wx k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (wx k) (Sum.inr i))
  simpa [wx] using h
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
