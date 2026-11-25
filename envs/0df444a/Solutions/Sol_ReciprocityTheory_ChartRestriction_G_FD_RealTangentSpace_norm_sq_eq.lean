-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.norm_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:48:22.055777+00:00
-- url     : https://prove2.me/submissions/83463318-4d94-4cd0-bdb9-828ea9a06d5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_inner_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
variable [hz : Fact (z ∈ X.dom)]
namespace ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
theorem _root_.solution (u : VT (X := X) z ξ) : ‖u‖ ^ 2 = ∑ τ, X.maj z τ (u.val τ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq, MajorantOperators.gI_self hz.out]
end ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
