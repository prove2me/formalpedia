-- Prove2me | solution 1 for UpperTheory.Reformulated.B.DYhb7.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:06.723423+00:00
-- url     : https://prove2.me/submissions/5e8ae4e8-bc69-46bb-8f61-c6b2c2404f0b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumEmbeddingsEqRealAddComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.DYhb7
open NumberField NumberField.InfinitePlace Finset
private lemma algebra_trace_pi_eq_sum_trace {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    [Module.Free ℝ A] [Module.Finite ℝ A] (x : ι → A) :
    Algebra.trace ℝ (ι → A) x = ∑ i, Algebra.trace ℝ A (x i) := by
  classical
  let b := Module.Free.chooseBasis ℝ A
  let B := Pi.basis (fun _ : ι => b)
  rw [Algebra.trace_eq_matrix_trace B]
  simp_rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  simp [B, Pi.basis_apply, Pi.basis_repr, Pi.mul_apply]
open scoped Classical in
private lemma fiber_embeddings_eq_pair {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    ({φ | mk φ = w} : Finset (F →+* ℂ)) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  conv_lhs => rw [← mk_embedding w, mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; simp [ComplexEmbedding.conjugate])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; simp [ComplexEmbedding.conjugate])
open scoped Classical in
private lemma sum_embeddings_eq_real_add_complex {F : Type} [Field F] [NumberField F] (y : F) :
    ∑ φ : F →+* ℂ, φ y =
      (∑ w : {w : InfinitePlace F // IsReal w}, (embedding_of_isReal w.2 y : ℂ)) +
      ∑ w : {w : InfinitePlace F // IsComplex w}, (((2 * (w.1.embedding y).re : ℝ)) : ℂ) := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => mk φ), sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, conjugate_embedding_eq_of_isReal w.2]
    simp
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, Finset.sum_pair]
    · rw [ComplexEmbedding.conjugate_coe_eq]
      push_cast
      rw [Complex.add_conj]
      push_cast
      rfl
    · intro h
      exact (isComplex_iff.mp w.2) (ComplexEmbedding.isReal_iff.mpr h.symm)
end UpperTheory.Reformulated.B.DYhb7
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYhb7
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
      (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
          ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
        (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  apply Complex.ofReal_injective
  have h1 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ y := by
    have := _root_.trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f y) _ fun _ => by
      simp [RingHom.equivRatAlgHom_apply]).symm
  rw [Complex.ofReal_ratCast, h1, UpperTheory.Reformulated.B.DYhb7.sum_embeddings_eq_real_add_complex, Algebra.trace_prod_apply,
    UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace, UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace]
  simp [Algebra.trace_complex_apply]
end UpperTheory.Reformulated.B.DYhb7
