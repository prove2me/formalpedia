-- Prove2me | solution 1 for ReciprocityTheory.PGsh.mem_span_pow_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:36.564278+00:00
-- url     : https://prove2.me/submissions/4a064b6c-82cf-48dd-92eb-61e0c95c891a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution {P : MvPolynomial (Fin d) R}
    (h : ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → coeff β P = 0) :
    P ∈ Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p) := by
  classical
  rw [P.as_sum]
  refine Ideal.sum_mem _ fun β hβ => ?_
  have hnot : ¬ ∀ j, β j < p := fun h' => (mem_support_iff.1 hβ) (h β h')
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  have e : monomial β (coeff β P) = X j ^ p * monomial (β - Finsupp.single j p) (coeff β P) := by
    have hs : Finsupp.single j p + (β - Finsupp.single j p) = β := by
      ext l
      by_cases hl : j = l
      · subst hl
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same]
        omega
      · simp [hl]
    rw [X_pow_eq_monomial, monomial_mul, one_mul, hs]
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
end ReciprocityTheory.PGsh
