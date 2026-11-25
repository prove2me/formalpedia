-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:28.631716+00:00
-- url     : https://prove2.me/submissions/5cb37ce1-03ae-4d57-a1af-ae24b20f94af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_zero_of_exp_eq_one

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
    (h : PowerSeries.subst a (PowerSeries.exp k) = PowerSeries.subst b (PowerSeries.exp k)) : a = b := by
  have hab : constantCoeff (a - b) = 0 := by simp [ha, hb]
  have h1 := exp_add hab hb
  rw [sub_add_cancel, h] at h1
  have hu : IsUnit (PowerSeries.subst b (PowerSeries.exp k)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_exp hb]; exact isUnit_one)
  have h3 : 1 * PowerSeries.subst b (PowerSeries.exp k) =
      PowerSeries.subst (a - b) (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k) :=
    (one_mul _).trans h1
  exact sub_eq_zero.mp (eq_zero_of_exp_eq_one hab (hu.mul_right_cancel h3).symm)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
