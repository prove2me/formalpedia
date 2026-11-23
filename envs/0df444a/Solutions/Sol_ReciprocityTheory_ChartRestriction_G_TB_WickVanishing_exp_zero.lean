-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:08.445797+00:00
-- url     : https://prove2.me/submissions/e67b09ce-a5c9-4fd1-9a05-edd7b91fc14d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_exp
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
private theorem powerSeries_subst_zero_eq_C_constantCoeff (f : PowerSeries k) :
    PowerSeries.subst (0 : MvPowerSeries σ k) f = MvPowerSeries.C (PowerSeries.constantCoeff f) := by
  classical
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
    finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  by_cases he : e = 0
  · subst he; simp
  · simp only [smul_eq_mul, pow_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [MvPowerSeries.coeff_one, if_neg he, mul_zero, MvPowerSeries.coeff_C, if_neg he]
end General
section Inj
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
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
theorem _root_.solution : PowerSeries.subst (0 : MvPowerSeries σ k) (PowerSeries.exp k) = 1 := by
  rw [powerSeries_subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
