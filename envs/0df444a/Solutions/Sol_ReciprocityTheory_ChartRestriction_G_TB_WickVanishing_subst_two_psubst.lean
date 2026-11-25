-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_two_psubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:55.586821+00:00
-- url     : https://prove2.me/submissions/6e380cd0-219f-41f0-97a3-97a6c8f60937

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_two

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (Y : MvPowerSeries (Fin 2) k) (hY : constantCoeff Y = 0) (f : PowerSeries k) :
    MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ k) (PowerSeries.subst Y f) =
      PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ k) Y) f := by
  have hY' := (PowerSeries.HasSubst.of_constantCoeff_zero hY).const
  exact MvPowerSeries.subst_comp_subst_apply hY' (hasSubst_two ha hb) f
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
