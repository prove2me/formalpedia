-- Prove2me | solution 1 for RandomDimReduction.Channel.Supplement.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:23:43.744203+00:00
-- url     : https://prove2.me/submissions/fac245f2-b07d-4aa5-b507-1646e6ce6633

import Definitions.Def_RandomDimReduction_Channel_Supplement_Purification

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker Matrix ComplexConjugate Matrix.Norms.Elementwise
namespace RandomDimReduction.Channel.Supplement

theorem lemma_2_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    (∀ X : Matrix b a ℂ,
      ((1 : Op a) ⊗ₖ X).mulVec (gamma a) =
        (Xᵀ ⊗ₖ (1 : Op b)).mulVec (gamma b)) ∧
    (∀ X Y : Matrix b a ℂ,
      WildeQIT.partialTraceRight
        ((X ⊗ₖ (1 : Op a)) * MixedCloning.Optimal.pure (gamma a) *
          (Yᴴ ⊗ₖ (1 : Op a))) = X * Yᴴ) := by
  constructor
  · intro X
    funext ⟨i, j⟩
    simp [Matrix.mulVec, dotProduct, gamma, Fintype.sum_prod_type, Matrix.one_apply,
      kroneckerMap_apply]
  · intro X Y
    ext i j
    simp [WildeQIT.partialTraceRight, Matrix.mul_apply, MixedCloning.Optimal.pure, gamma,
      Fintype.sum_prod_type, Matrix.one_apply, kroneckerMap_apply]

end RandomDimReduction.Channel.Supplement

open RandomDimReduction.Channel RandomDimReduction.Channel.Supplement in
theorem solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    (∀ X : Matrix b a ℂ,
      ((1 : Op a) ⊗ₖ X).mulVec (gamma a) =
        (Xᵀ ⊗ₖ (1 : Op b)).mulVec (gamma b)) ∧
    (∀ X Y : Matrix b a ℂ,
      WildeQIT.partialTraceRight
        ((X ⊗ₖ (1 : Op a)) * MixedCloning.Optimal.pure (gamma a) *
          (Yᴴ ⊗ₖ (1 : Op a))) = X * Yᴴ) :=
  RandomDimReduction.Channel.Supplement.lemma_2_1
