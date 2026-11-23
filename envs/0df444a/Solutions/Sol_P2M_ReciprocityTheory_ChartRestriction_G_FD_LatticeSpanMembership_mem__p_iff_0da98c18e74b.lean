-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:57.084932+00:00
-- url     : https://prove2.me/submissions/c8a8657f-09da-4565-af2d-0d9a159d56da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
theorem _root_.solution {ξ μ : Fin r → E} : μ ∈ X.Λp ξ ↔ μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0 := by
  unfold Data.Λp
  rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
