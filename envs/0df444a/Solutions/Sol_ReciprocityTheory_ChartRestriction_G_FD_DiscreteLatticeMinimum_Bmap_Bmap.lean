-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.Bmap_Bmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:31:45.457795+00:00
-- url     : https://prove2.me/submissions/c5e1da82-614a-4ed6-b6f2-e7f6cc8c6887

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Bop_Bop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
theorem _root_.solution (u : VT (X := Y.toData) z ξ) : Bmap z ξ (Bmap z ξ u) = (-(Y.k0 ^ 2)) • u := by
  apply VT.ext
  rw [Bmap_val, Bmap_val, MajorantOperators.Bop_Bop hz.out]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
