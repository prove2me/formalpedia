-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.qb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:22.639527+00:00
-- url     : https://prove2.me/submissions/3fecff07-45df-46d6-b2ea-6d65069e32db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings

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
namespace ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
theorem _root_.solution {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) (i : ι) : qb X g i = (g i : Fin r → E) := by
  unfold qb
  exact Basis.mk_apply _ _ _
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
