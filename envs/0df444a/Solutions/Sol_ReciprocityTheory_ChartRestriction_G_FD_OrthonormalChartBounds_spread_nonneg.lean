-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.spread_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:04.603836+00:00
-- url     : https://prove2.me/submissions/c35eef68-f155-40d2-a20c-6f80c97b04a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PivotNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · simp [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
  · exact sub_nonneg.mpr (ciInf_le_ciSup (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove)
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
