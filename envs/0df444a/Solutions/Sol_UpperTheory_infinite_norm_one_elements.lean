-- Prove2me | solution 1 for UpperTheory.infinite_norm_one_elements
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:44.625385+00:00
-- url     : https://prove2.me/submissions/34f62b8e-6589-40e2-8523-305675e1d662

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteNormOneElements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by
  intro F E _ _ _ _ σ hE hσ
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)
  generalize w.embedding = τ at hw
  have hinv : ∀ x : E, σ (σ x) = x := fun x =>
    τ.injective (by rw [hσ, hσ, star_star])
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [h] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  have h1 : ∀ n : ℕ, (n : E) + a ≠ 0 := by
    intro n hn
    apply ha
    have : a = -(n : E) := by linear_combination hn
    rw [this, map_neg, map_natCast]
  have h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0 := by
    intro n hn
    apply h1 n
    have := congrArg σ hn
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_
  · intro m n hmn
    have h3 := (div_eq_div_iff (h2 m) (h2 n)).mp hmn
    have h4 : ((m : E) - n) * (σ a - a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact Nat.cast_injective (R := E) (sub_eq_zero.mp h)
    · exact absurd (sub_eq_zero.mp h) ha
  · intro n
    show _ * σ _ = 1
    rw [map_div₀, map_add, map_add, map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]
end UpperTheory
