-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.wv_dot_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:54.310393+00:00
-- url     : https://prove2.me/submissions/6a3a3d04-0c03-4dee-996a-60a28242ccb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_wv_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    wv X ξ τ ⬝ᵥ Data.emb τ.1 ξ = 0 := by
  rw [wv_dot]
  exact (hermC_emb τ.1 X.Gm ξ ξ).trans (by rw [hξ, map_zero])
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
