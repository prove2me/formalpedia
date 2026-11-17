-- Prove2me | solution 1 for RingHom.Locally.isStandardSmoothOfRelativeDimension_of_jacobian_span
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:24.014669+00:00
-- url     : https://prove2.me/submissions/223ae659-e04e-4c6f-9e85-30263f4c9ecf

import Mathlib
import Theorems.Thm_Algebra_PreSubmersivePresentation_isStandardSmoothOfRelativeDimension_localizationAway_jacobian

/-! Local smoothness with a fixed relative dimension from spanning selected Jacobians. -/
noncomputable section

universe u

namespace RingHom

/-- If equal-dimensional finite selected presentations have Jacobians
spanning the unit ideal, the map is locally standard smooth in that relative
dimension. -/
theorem _root_.solution
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {E ι σ : Type*} [_root_.Finite ι] [_root_.Finite σ]
    (P : E → Algebra.PreSubmersivePresentation R S ι σ) {n : ℕ}
    (hDimension : ∀ e, (P e).dimension = n)
    (hspan : Ideal.span (Set.range fun e ↦ (P e).jacobian) = ⊤) :
    Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap R S) := by
  refine ⟨Set.range fun e ↦ (P e).jacobian, hspan, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact (P e).isStandardSmoothOfRelativeDimension_localizationAway_jacobian
    (hDimension e)

end RingHom
