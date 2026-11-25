-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.inner_Bmap_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:18:27.062889+00:00
-- url     : https://prove2.me/submissions/1af4789f-6eab-4a52-af5f-8e06d0da2e8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_Bop_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_inner_eq


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
theorem _root_.solution (u v : VT (X := Y.toData) z ξ) :
    inner ℝ u (Bmap z ξ v) = -inner ℝ (Bmap z ξ u) v := by
  rw [inner_eq, inner_eq, Bmap_val, Bmap_val, MajorantOperators.gI_Bop_right hz.out]
end ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
