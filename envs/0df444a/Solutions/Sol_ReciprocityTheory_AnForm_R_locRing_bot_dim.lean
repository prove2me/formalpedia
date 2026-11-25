-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.locRing_bot_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:20.300205+00:00
-- url     : https://prove2.me/submissions/45d74f2f-4925-46e4-a1bb-08a71f56a16c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
import Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_of_jacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
private theorem locRing_bot_fin_zero_regular_and_dim_zero (p : Fin 0 → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) ∧
      ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) = ((0 - 0 : ℕ) : WithBot ℕ∞) := by
  refine isRegularLocalRing_of_jacobian (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p ?_
    (fun i : Fin 0 => i.elim0) (fun i => i.elim0) linearIndependent_empty_type ?_
  · intro h hh
    rw [Ideal.mem_bot] at hh
    simp [hh]
  · refine ⟨⊥, ?_, bot_le, by simp⟩
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
end
end ReciprocityTheory.AnForm.R
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (p : Fin 0 → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) = 0 := by
  simpa using (locRing_bot_fin_zero_regular_and_dim_zero p).2
end ReciprocityTheory.AnForm.R
