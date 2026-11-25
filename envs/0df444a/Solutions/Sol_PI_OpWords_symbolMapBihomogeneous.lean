-- Prove2me | solution 1 for PI.OpWords.symbolMapBihomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:44.764419+00:00
-- url     : https://prove2.me/submissions/c08312e9-8acb-4a3c-b9db-134634717c65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Theorems.Thm_PI_OpWords_coeff_kappa
import Theorems.Thm_PI_OpWords_degree_of_coeff_ne
import Theorems.Thm_PI_OpWords_exists_sumElim
import Theorems.Thm_PI_OpWords_weight_wx
import Theorems.Thm_PI_OpWords_weight_wxi


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
theorem _root_.solution : KappaBihom := by
  intro K _ _ k d A
  show kappa K k d A ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  have key : ∀ m g : Fin k →₀ ℕ, coeff (Finsupp.sumElim m g) (kappa K k d A) ≠ 0 →
      m.degree = d ∧ g.degree = d := by
    intro m g h
    rw [coeff_kappa] at h
    have h2 : coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) ≠ 0 := right_ne_zero_of_mul h
    refine ⟨degree_of_coeff_ne _ h2, ?_⟩
    by_contra hg
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dif_neg hg]
    rw [h0, map_zero] at h2
    simp at h2
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩ <;> rw [mem_weightedHomogeneousSubmodule] <;> intro n hn <;>
    obtain ⟨m, g, rfl⟩ := exists_sumElim n
  · rw [weight_wx]
    exact (key m g hn).1
  · rw [weight_wxi]
    exact (key m g hn).2
end PI.OpWords
