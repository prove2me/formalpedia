-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_gram_re_le_prod_norm_sq_50acf4657243
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:13.621723+00:00
-- url     : https://prove2.me/submissions/b2b4835d-dd30-4f16-b793-9d6b6bc70afc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    (det (gram ℂ v)).re ≤ ∏ i, ‖v i‖ ^ 2 := by
  set W := Submodule.span ℂ (Set.range v)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let w : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hgw : gram ℂ v = gram ℂ w := by
    ext i j
    simp only [gram_apply, w, Submodule.coe_inner]
  have hfin : Module.finrank ℂ W = Fintype.card (Fin n) := finrank_span_eq_card hv
  let b : OrthonormalBasis (Fin n) ℂ W := gramSchmidtOrthonormalBasis hfin w
  have hb : b.toBasis.det w = ∏ i, inner ℂ (b i) (w i) := gramSchmidtOrthonormalBasis_det hfin w
  set A := b.toBasis.toMatrix w
  have hA : gram ℂ w = Aᴴ * A := by
    ext j k
    rw [gram_apply, mul_apply, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [A, conjTranspose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, RCLike.star_def,
      inner_conj_symm]
  have hdet : (det (gram ℂ w)).re = ‖b.toBasis.det w‖ ^ 2 := by
    rw [hA, det_mul, det_conjTranspose, Module.Basis.det_apply, RCLike.star_def, Complex.conj_mul']
    norm_cast
  rw [hgw, hdet, hb, norm_prod, ← Finset.prod_pow]
  gcongr with i
  calc ‖inner ℂ (b i) (w i)‖ ≤ ‖b i‖ * ‖w i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]; rfl
end GroundTheory.Heights₂.Heights.LatticeLemmas
