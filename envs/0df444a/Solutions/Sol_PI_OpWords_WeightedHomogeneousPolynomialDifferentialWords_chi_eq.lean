-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:49.076635+00:00
-- url     : https://prove2.me/submissions/6590ebdc-3669-4064-b911-ae584034bbc8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_chi_monomial

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
theorem _root_.solution (i0 : Fin k) (d : ℕ) (f : Pol K k) (hf : IsWeightedHomogeneous (wxi k) f d) :
    aeval (chiF K i0) f = X (Sum.inl i0) ^ d * f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [chi_monomial, hf (mem_support_iff.1 hm)]
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
