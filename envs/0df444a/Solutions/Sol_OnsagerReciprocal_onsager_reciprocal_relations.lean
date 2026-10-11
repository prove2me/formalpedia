-- Prove2me | solution 1 for OnsagerReciprocal.onsager_reciprocal_relations
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T23:48:17.791002+00:00
-- url     : https://prove2.me/submissions/2f570d30-61b8-4b07-b878-1f8653d4ce02

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic
import Theorems.Thm_OnsagerReciprocal_conjugate_fluctuation_average
import Theorems.Thm_OnsagerReciprocal_reciprocity_at_time_zero

open Matrix
set_option autoImplicit false

/-- Onsager's principle as a reduction: the time-zero reciprocity
`Σₗ γᵢₗ ⟨Xₗ xₖ⟩ = Σₗ γₖₗ ⟨Xₗ xᵢ⟩` combined with the Gaussian moment identity `⟨Xₗ xₖ⟩ = δₗₖ`
collapses both sums to single terms, giving `γᵢₖ = γₖᵢ`. -/
theorem solution {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef)
    (hrev : ∀ t : ℝ, 0 ≤ t → ∀ i k : Fin n,
      OnsagerReciprocal.timeCorrelation β lam t i k =
        OnsagerReciprocal.timeCorrelation β lam t k i) :
    ∀ i k : Fin n, OnsagerReciprocal.kineticCoeff β lam i k =
      OnsagerReciprocal.kineticCoeff β lam k i := by
  intro i k
  have h := OnsagerReciprocal.reciprocity_at_time_zero β lam hβ hrev i k
  simp only [OnsagerReciprocal.conjugate_fluctuation_average β hβ, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h
