-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:14.811032+00:00
-- url     : https://prove2.me/submissions/f1a50b7d-a983-4a38-88a9-ff8cbaa7114a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log_one_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Two
variable (k : Type) [CommRing k] [Algebra ℚ k]
end Two
section General
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
private theorem powerSeries_subst_one (a : MvPowerSeries σ k) :
    PowerSeries.subst a (1 : PowerSeries k) = 1 := by
  rw [show (1 : PowerSeries k) = PowerSeries.C (1 : k) from (map_one _).symm, PowerSeries.subst_C,
    map_one]
end General
section Inj
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
private theorem constantCoeff_log_eq_zero_wick_vanishing : PowerSeries.constantCoeff (PowerSeries.log k) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_log]
  simp
end Inj
section Log
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
end Log
section Props
end Props
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {f : MvPowerSeries σ k} (hf : constantCoeff f = 1) :
    PowerSeries.subst (PowerSeries.subst (f - 1) (PowerSeries.log k)) (PowerSeries.exp k) = f := by
  have hb : PowerSeries.HasSubst (f - 1) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hf])
  have ha : PowerSeries.HasSubst (PowerSeries.log k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_log_eq_zero_wick_vanishing
  rw [← PowerSeries.subst_comp_subst_apply ha hb, exp_log_one_add, PowerSeries.subst_add hb,
    PowerSeries.subst_X hb, powerSeries_subst_one]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
