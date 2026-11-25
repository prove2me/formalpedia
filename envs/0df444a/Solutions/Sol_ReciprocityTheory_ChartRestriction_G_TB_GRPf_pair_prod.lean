-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.pair_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:29.092155+00:00
-- url     : https://prove2.me/submissions/b1717aab-c07b-45f6-b209-134937e88aac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_two_mul_eq_zero

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
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution (c : k) (s s' : O →+* k)
    (h : ∀ a, c * (s a * s (star a) + s' a * s' (star a) - 2 * s a * s' a) = 0) (a : O) :
    c * ((s a - s (star a)) * (s a - s' (star a))) = 0 := by
  apply two_mul_eq_zero
  have h0 := h a
  have h1 := h (a + 1)
  have h2 := h (a * a)
  have h3 := h (a * a + 1)
  simp only [map_add, map_one, map_mul, star_add, star_one, star_mul] at h1 h2 h3
  linear_combination (-1 : k) * (h3 - h2) + (s' a + s (star a) + s' (star a) - s a) * (h1 - h0)
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
