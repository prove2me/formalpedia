-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.Tm_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:03.695001+00:00
-- url     : https://prove2.me/submissions/7d3b559f-e30a-49a5-b773-f1a41f104d58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
open NumberField Module Submodule
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
theorem _root_.solution : Function.Injective (Tm X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  ext w
  obtain ⟨τ, hτ⟩ : ∃ τ : X.Ψ, plc X τ = w := by
    by_cases h : w.1.embedding ∈ X.Ψ
    · exact ⟨⟨_, h⟩, Subtype.ext (InfinitePlace.mk_embedding w.1)⟩
    · have h2 : ComplexEmbedding.conjugate w.1.embedding ∈ X.Ψ :=
        (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact h)
      exact ⟨⟨_, h2⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans
        (InfinitePlace.mk_embedding w.1))⟩
  have h3 := congrFun hz τ
  simp only [Tm, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h3
  subst hτ
  split_ifs at h3
  · simpa using h3
  · simpa using h3
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
