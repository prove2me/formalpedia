-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:00.699357+00:00
-- url     : https://prove2.me/submissions/75030039-addd-41be-b284-e93d3bdc5226

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_two_psubst

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
theorem _root_.solution {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (a + b) (PowerSeries.exp k) =
      PowerSeries.subst a (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k) := by
  have hab := hasSubst_two ha hb
  have h0 : constantCoeff ((X 0 : MvPowerSeries (Fin 2) k) + X 1) = 0 := by simp
  have e1 := subst_two_psubst ha hb _ h0 (PowerSeries.exp k)
  rw [exp_two k, MvPowerSeries.subst_mul hab, subst_two_psubst ha hb _ (by simp),
    subst_two_psubst ha hb _ (by simp), MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab,
    MvPowerSeries.subst_X hab] at e1
  simpa using e1.symm
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
