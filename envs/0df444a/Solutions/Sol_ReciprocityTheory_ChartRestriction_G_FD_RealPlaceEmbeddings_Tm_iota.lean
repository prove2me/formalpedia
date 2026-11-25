-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.Tm_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:07.630623+00:00
-- url     : https://prove2.me/submissions/ea6139d4-3e1c-442a-b184-706f0d893d8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_iota_apply


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
theorem _root_.solution (x : E) (τ : X.Ψ) : Tm X (TraceIntegralBasis.iota E x) τ = τ.1 x := by
  simp only [Tm, LinearMap.coe_mk, AddHom.coe_mk, TraceIntegralBasis.iota_apply]
  split_ifs with h
  · rw [h]
  · rcases InfinitePlace.embedding_mk_eq τ.1 with h' | h'
    · exact absurd h' h
    · change conj ((InfinitePlace.mk τ.1).embedding x) = τ.1 x
      rw [h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
