-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.EF_eq_efr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:25:38.677672+00:00
-- url     : https://prove2.me/submissions/3741bb14-efc6-466a-9dbb-1183b3cd6de7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_trace_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
theorem _root_.solution (X : Data E r) (x y : Fin r → E) :
    ((EFf X.ξ0 X.Gm x y : ℚ) : ℝ) = efr X (X.embV x) (X.embV y) := by
  unfold EFf efr
  rw [trace_re X]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul]
  congr 3
  simp only [herm, hermC, map_sum, map_mul, ReciprocityTheory.ChartRestriction.G.FD.emb_cc, Data.embV, Data.emb]
end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
