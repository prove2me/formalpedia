-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_span_901177580971
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:01.16595+00:00
-- url     : https://prove2.me/submissions/b90b362c-0cf1-4ca5-8016-a6324974f34f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (N : ℕ) :
    originIdeal n ^ N ≤
      Ideal.span {p | ∃ m : Fin n →₀ ℕ, m.degree = N ∧ monomial m (1 : ℂ) = p} := by
  induction N with
  | zero => simp only [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
            exact Ideal.subset_span ⟨0, by simp, by simp⟩
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [originIdeal, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨m + Finsupp.single i 1, by simp [hm], by simp [X, monomial_mul]⟩
end GroundTheory.Heights₂.Heights.ComplexSets
