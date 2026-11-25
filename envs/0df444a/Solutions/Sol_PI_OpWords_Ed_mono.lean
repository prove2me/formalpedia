-- Prove2me | solution 1 for PI.OpWords.Ed_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:08:05.632811+00:00
-- url     : https://prove2.me/submissions/dea4d099-b63c-4530-83da-034849294ee3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Theorems.Thm_PI_OpWords_mono_val
import Theorems.Thm_PI_OpWords_degree_sub_add
import Theorems.Thm_PI_OpWords_Ed_val

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
theorem _root_.solution (a b : Fin k) (g : Fin k →₀ ℕ) :
    Formalism.MainNotions.TestSideCounting.Ed K k d a b (mono K k d g) =
      ((g b : ℕ) : K) • mono K k d (g - single b 1 + single a 1) := by
  apply Subtype.ext
  rw [Ed_val, Submodule.coe_smul, mono_val, mono_val]
  by_cases hb : g b = 0
  · split_ifs <;> simp [pderiv_monomial, hb]
  · rw [degree_sub_add g a b hb]
    split_ifs with h
    · rw [pderiv_monomial, X, monomial_mul, smul_monomial, add_comm (Finsupp.single a 1)]
      simp
    · simp
end PI.OpWords
