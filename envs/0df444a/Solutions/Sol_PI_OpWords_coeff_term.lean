-- Prove2me | solution 1 for PI.OpWords.coeff_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:27.593705+00:00
-- url     : https://prove2.me/submissions/4f190448-9441-482d-a3e2-2fdcf23c4322

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Theorems.Thm_PI_OpWords_mapDomain_inl_add_inr
import Theorems.Thm_PI_OpWords_sumElim_inj

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
theorem _root_.solution (P : MvPolynomial (Fin k) K) (m g g' : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (rename Sum.inl P * monomial (g'.mapDomain Sum.inr) (1 : K)) =
      if g' = g then coeff m P else 0 := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [rename_monomial, monomial_mul, mapDomain_inl_add_inr]
    simp only [coeff_monomial, sumElim_inj, mul_one]
    by_cases h1 : u = m <;> by_cases h2 : g' = g <;> simp [h1, h2]
  next p q hp hq =>
    rw [map_add, add_mul, coeff_add, hp, hq]
    split_ifs <;> simp [coeff_add]
end PI.OpWords
