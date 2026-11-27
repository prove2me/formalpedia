-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.efr_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:25:41.891804+00:00
-- url     : https://prove2.me/submissions/2381d3bb-5198-413f-ac19-20bc12489b6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence

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
theorem _root_.solution (X : Data E r) (v v' w : X.Ψ → Fin r → ℂ) :
    efr X (v + v') w = efr X v w + efr X v' w := by
  unfold efr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, Complex.add_re]
end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
