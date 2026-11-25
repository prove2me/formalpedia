-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.cc_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:25.148728+00:00
-- url     : https://prove2.me/submissions/30742643-70d1-46e4-9a55-63b076259904

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_coeff_scale

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
theorem _root_.solution (a : O) {f : MvPowerSeries (GLet T rk) k} (hf : constantCoeff f = 0) :
    constantCoeff (scaleBy χ a f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_scale,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
