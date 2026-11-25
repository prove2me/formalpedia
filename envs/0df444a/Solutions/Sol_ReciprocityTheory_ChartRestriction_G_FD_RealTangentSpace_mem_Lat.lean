-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.mem_Lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:03:06.475954+00:00
-- url     : https://prove2.me/submissions/86664c45-1534-46de-b4bc-77f22d44419b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace

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
theorem _root_.solution (hξ : X.IsIso ξ) {a : VT (X := X) z ξ} : a ∈ Lat z ξ hξ ↔ ∃ μ, phi z ξ hξ μ = a := by
  show a ∈ (phi z ξ hξ).range ↔ _
  exact AddMonoidHom.mem_range
end ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
