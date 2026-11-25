-- Prove2me | solution 1 for ReciprocityTheory.Cheb.filter_infinitePlace_mk_eq_embedding_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:54.495401+00:00
-- url     : https://prove2.me/submissions/b626c10b-5b90-4019-9109-e1ab63c467f3

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf

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
theorem _root_.solution (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hφ
    rcases InfinitePlace.mk_eq_iff.mp (hφ.trans (InfinitePlace.mk_embedding w).symm) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; exact (star_involutive φ).symm)
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
end ReciprocityTheory.Cheb
