-- Prove2me | solution 1 for PI.OpWords.symbolMapMulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:06.837711+00:00
-- url     : https://prove2.me/submissions/7044da95-da8c-497c-bd76-2c8398e2f1de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Theorems.Thm_PI_OpWords_Ed_mono
import Theorems.Thm_PI_OpWords_coeff_kappa
import Theorems.Thm_PI_OpWords_invFact_add_single
import Theorems.Thm_PI_OpWords_pol_ext
import Theorems.Thm_PI_OpWords_sumElim_add_single_inr
import Theorems.Thm_PI_OpWords_sumElim_sub_single_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Finsupp
noncomputable section
namespace PI.OpWords
private theorem coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth {σ : Type} {K : Type} [Field K] (i : σ) (P : MvPolynomial σ K)
    (n : σ →₀ ℕ) : coeff n (pderiv i P) = coeff (n + Finsupp.single i 1) P * ((n i : K) + 1) := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = n + Finsupp.single i 1
    · subst h
      simp
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have hu : u i = 0 := by
          by_contra hne
          apply h
          rw [← h2, tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]
          omega
        simp [hu]
      · rfl
  next p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]
end PI.OpWords
end
end

set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution : KappaRight := by
  intro K _ _ k d a b A
  apply pol_ext
  intro m g
  rw [coeff_kappa, Module.End.mul_apply, Ed_mono, map_smul, Submodule.coe_smul, coeff_smul, coeff_X_mul']
  by_cases hb : g b = 0
  · rw [if_neg (by simp [hb])]
    simp [hb]
  · rw [if_pos (by simp [hb]), sumElim_sub_single_inr, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, sumElim_add_single_inr, coeff_kappa]
    simp only [Finsupp.sumElim_apply, Sum.elim_inr]
    have h1 := invFact_add_single (K := K) (g - single b 1) a
    have h2 := invFact_add_single (K := K) (g - single b 1) b
    have hle : single b 1 ≤ g := by
      rw [Finsupp.single_le_iff]
      omega
    rw [tsub_add_cancel_of_le hle] at h2
    have h3 : ((g - single b 1 : Fin k →₀ ℕ) b : K) + 1 = (g b : K) := by
      have h4 : (g - single b 1 : Fin k →₀ ℕ) b + 1 = g b := by
        simp
        omega
      exact_mod_cast h4
    rw [h3] at h2
    linear_combination (coeff m (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K)) * h2 -
      (coeff m (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K)) * h1
end PI.OpWords
