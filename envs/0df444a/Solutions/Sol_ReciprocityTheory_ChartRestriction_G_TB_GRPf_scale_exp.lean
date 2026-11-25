-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.scale_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:26.197995+00:00
-- url     : https://prove2.me/submissions/0f3d5f7f-7c6f-4ab4-a48d-a55d20aacbc1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


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
    scaleBy χ a (PowerSeries.subst f (PowerSeries.exp k)) = PowerSeries.subst (scaleBy χ a f) (PowerSeries.exp k) := by
  unfold scaleBy
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst]
  refine WickVanishing.subst_exp _ (fun s => ?_) hf
  simp
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
