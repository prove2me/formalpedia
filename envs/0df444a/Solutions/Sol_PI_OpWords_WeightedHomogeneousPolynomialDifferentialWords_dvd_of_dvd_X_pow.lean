-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.dvd_of_dvd_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:29.78745+00:00
-- url     : https://prove2.me/submissions/b0ac4beb-a4a2-41cd-acd0-268a4399e3ff

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
theorem _root_.solution {i : Fin k ⊕ Fin k} {s f : Pol K k} (hs : ¬ (X i : Pol K k) ∣ s) :
    ∀ n : ℕ, s ∣ X i ^ n * f → s ∣ f
  | 0, h => by simpa using h
  | n + 1, h => by
    rw [pow_succ', mul_assoc] at h
    rcases dvd_X_mul_iff.1 h with h' | ⟨h', _⟩
    · exact solution hs n h'
    · exact absurd h' hs
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
