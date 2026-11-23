-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.mem_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:38.843848+00:00
-- url     : https://prove2.me/submissions/0677f910-c857-463c-8592-58fe5ccf1b2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
theorem _root_.solution (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hx : x ∈ X.L') :
    ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
  obtain ⟨hξΛ, -, -⟩ := hξ
  intro i
  fin_cases i
  · exact hξΛ
  · exact X.NC_sub x hx
end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
