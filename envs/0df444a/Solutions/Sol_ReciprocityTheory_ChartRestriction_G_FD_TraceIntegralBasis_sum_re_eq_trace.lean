-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.sum_re_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:47.12354+00:00
-- url     : https://prove2.me/submissions/e198bdf8-15ca-4b8f-bfba-b003c7c8df2e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
theorem _root_.solution (u : E) :
    ∑ w : CP E, (w.1.embedding u).re = (1 / 2 : ℝ) * (Algebra.trace ℚ E u : ℝ) := by
  have hall : ∀ w : InfinitePlace E, IsComplex w := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mp fun hw =>
      IsEmpty.false (⟨w, hw⟩ : {w : InfinitePlace E // IsReal w})
  have hfib : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ u =
        w.embedding u + conj (w.embedding u) := by
    intro w
    have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hall w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
    have hset : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
          rw [h, InfinitePlace.mk_embedding]
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
        · exact Or.inl h1
        · right
          rw [← h1, conj_conj]
      · rintro (rfl | rfl)
        · exact InfinitePlace.mk_embedding w
        · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [hset, Finset.sum_pair hne.symm, ComplexEmbedding.conjugate_coe_eq]
  have h0 : algebraMap ℚ ℂ (Algebra.trace ℚ E u) = ∑ σ : E →ₐ[ℚ] ℂ, σ u := by
    first
      | exact trace_eq_sum_embeddings ℂ
      | exact trace_eq_sum_embeddings ℂ (x := u)
      | exact trace_eq_sum_embeddings (E := ℂ) (x := u)
      | exact Algebra.trace_eq_sum_embeddings ℂ
  have h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ u = ∑ φ : E →+* ℂ, φ u :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ u)
      (fun σ : E →ₐ[ℚ] ℂ => σ u)
      (fun _ => rfl)).symm
  have h2 : ∑ φ : E →+* ℂ, φ u =
      ∑ w : InfinitePlace E, (w.embedding u + conj (w.embedding u)) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ u)]
    refine Finset.sum_congr rfl fun w _ => ?_
    first
      | exact hfib w
      | convert hfib w
  have h3 : ((Algebra.trace ℚ E u : ℚ) : ℂ) =
      ∑ w : CP E, (w.1.embedding u + conj (w.1.embedding u)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), h0, h1, h2]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ _ (fun _ => rfl)).symm
  have h4 := congrArg Complex.re h3
  rw [Complex.re_sum] at h4
  simp only [Complex.add_re, Complex.conj_re, Complex.ratCast_re] at h4
  rw [h4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
