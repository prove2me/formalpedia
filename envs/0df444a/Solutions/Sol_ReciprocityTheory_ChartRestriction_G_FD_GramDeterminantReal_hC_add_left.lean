-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:45.277109+00:00
-- url     : https://prove2.me/submissions/ac55b464-c4fb-4b42-a18e-b0305ffd50c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := (hL τ G v).map_add u u'
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
