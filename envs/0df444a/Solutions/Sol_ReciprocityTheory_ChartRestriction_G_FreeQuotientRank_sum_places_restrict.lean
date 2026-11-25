-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_places_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:19.377041+00:00
-- url     : https://prove2.me/submissions/fd280375-cd2d-43f4-ac23-60afafbb9f9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_sum_embeddings_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (g : (K →+* ℂ) → ℝ) (hg : ∀ τ, g ((starRingEnd ℂ).comp τ) = g τ) :
    ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * g (σ.embedding.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  rw [← sum_embeddings_restrict g]
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ∀ φ ∈ Finset.univ.filter (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ = σ),
      g (φ.comp (algebraMap K K₁)) = g (σ.embedding.comp (algebraMap K K₁)) := by
    intro φ hφ
    have h1 := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding σ, InfinitePlace.mk_eq_iff] at h1
    rcases h1 with h1 | h1
    · rw [h1]
    · rw [← h1]
      have h2 : (ComplexEmbedding.conjugate φ).comp (algebraMap K K₁)
          = (starRingEnd ℂ).comp (φ.comp (algebraMap K K₁)) := RingHom.ext fun x => rfl
      rw [h2, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
