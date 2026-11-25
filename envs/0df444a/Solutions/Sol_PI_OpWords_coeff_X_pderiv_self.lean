-- Prove2me | solution 1 for PI.OpWords.coeff_X_pderiv_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:09.825074+00:00
-- url     : https://prove2.me/submissions/8e45a005-98d5-48d4-b256-2746a63a6bfa

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
theorem _root_.solution {σ : Type} {K : Type} [Field K] (i : σ) (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : coeff m (X i * pderiv i f) = coeff m f * (m i : K) := by
  classical
  induction f using MvPolynomial.induction_on'
  next u a =>
    rw [pderiv_monomial]
    by_cases hu : u i = 0
    · by_cases h : u = m
      · subst h
        simp [hu]
      · simp [hu, coeff_monomial, h]
    · have hle : Finsupp.single i 1 ≤ u := by
        rw [Finsupp.single_le_iff]
        omega
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, coeff_monomial, coeff_monomial]
      split_ifs with h
      · subst h
        rfl
      · simp
  next p q hp hq =>
    simp only [map_add, mul_add, coeff_add, hp, hq, add_mul]
end PI.OpWords
