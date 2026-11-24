-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.nfac_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:25:51.458946+00:00
-- url     : https://prove2.me/submissions/91c27636-c2b7-478b-8040-ad734d3ba3f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
noncomputable section
open ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
theorem _root_.solution (la : Wt X.Ψ r) (x y : Frame X.Ψ r) :
    X.nfac la x / X.nfac la y = ∏ τ, rfac X la x y τ := by
  rw [Data.nfac, Data.nfac, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun τ _ => (Finset.prod_div_distrib _ _).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
