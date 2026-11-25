-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.prod_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:23.618791+00:00
-- url     : https://prove2.me/submissions/48e1f4a0-cdcf-45a7-9b0d-ee87822fc2f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution (m : GLet T rk →₀ ℕ) : (m.prod fun _ e => (2 : k) ^ e) = 2 ^ m.degree := by
  unfold Finsupp.prod Finsupp.degree
  exact Finset.prod_pow_eq_pow_sum _ _ _
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
