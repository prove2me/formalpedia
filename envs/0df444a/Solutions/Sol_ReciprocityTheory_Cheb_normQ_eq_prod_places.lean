-- Prove2me | solution 1 for ReciprocityTheory.Cheb.normQ_eq_prod_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:22.854993+00:00
-- url     : https://prove2.me/submissions/eab788c2-1eec-46e2-8fc9-41ffdff97144

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Theorems.Thm_ReciprocityTheory_Cheb_filter_infinitePlace_mk_eq_embedding_conjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
open NumberField.InfinitePlace
namespace ReciprocityTheory.Cheb
theorem _root_.solution (x : E) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = (∏ w : {w : InfinitePlace E // w.IsReal}, embedding_of_isReal w.2 x) *
      ∏ w : {w : InfinitePlace E // w.IsComplex}, (w.1 x) ^ 2 := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x),
    InfinitePlace.prod_eq_prod_mul_prod] at h
  rw [eq_ratCast] at h
  rw [Complex.ofReal_ratCast, h]
  push_cast
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [filter_infinitePlace_mk_eq_embedding_conjugate, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton,
      Finset.prod_singleton, embedding_of_isReal_apply]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding := by
      intro h'
      exact (not_isReal_iff_isComplex.mpr w.2) (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h'.symm))
    rw [filter_infinitePlace_mk_eq_embedding_conjugate, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj,
      ← Complex.sq_norm, norm_embedding_eq]
    push_cast
    rfl
end ReciprocityTheory.Cheb
