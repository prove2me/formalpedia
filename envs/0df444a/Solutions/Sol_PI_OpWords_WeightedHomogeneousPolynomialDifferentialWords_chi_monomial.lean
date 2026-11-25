-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:23.677613+00:00
-- url     : https://prove2.me/submissions/d3ee66d3-e90b-4608-93ee-0395fae1eb53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_chiF_eq

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
theorem _root_.solution (i0 : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) (c : K) :
    aeval (chiF K i0) (monomial m c : Pol K k) =
      X (Sum.inl i0) ^ (Finsupp.weight (wxi k) m) * monomial m c := by
  rw [aeval_monomial, monomial_eq, Finsupp.weight_apply, algebraMap_eq]
  simp only [chiF_eq, mul_pow, Finsupp.prod_mul, ← pow_mul']
  simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  ring
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
