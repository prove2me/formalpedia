-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_logS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:49.820074+00:00
-- url     : https://prove2.me/submissions/bbc771d9-9a87-438f-8a81-7a5cf504b955

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
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
    constantCoeff (PowerSeries.subst (f - 1) (PowerSeries.log k)) = 0 := PowerSeries.constantCoeff_subst_eq_zero (by simp [hf]) _ constantCoeff_log_eq_zero_wick_vanishing
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
