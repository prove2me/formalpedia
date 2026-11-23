-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.dot_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:11.532595+00:00
-- url     : https://prove2.me/submissions/29203b01-3643-42de-bb4e-37989c10426b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' (y i)
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
