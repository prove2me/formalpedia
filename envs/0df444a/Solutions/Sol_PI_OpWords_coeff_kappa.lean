-- Prove2me | solution 1 for PI.OpWords.coeff_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:49.069001+00:00
-- url     : https://prove2.me/submissions/a06d58fa-0334-4a31-ab79-1f09f168f355

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Theorems.Thm_PI_OpWords_coeff_term
import Theorems.Thm_PI_OpWords_mem_antidiag_iff
import Theorems.Thm_PI_OpWords_kappa_apply

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
theorem _root_.solution (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) (m g : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (kappa K k d A) =
      invFact K g * coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) := by
  classical
  rw [kappa_apply, coeff_sum]
  simp only [coeff_smul, coeff_term, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_antidiag_iff] at h
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dif_neg h]
    rw [h0, map_zero]
    simp
end PI.OpWords
