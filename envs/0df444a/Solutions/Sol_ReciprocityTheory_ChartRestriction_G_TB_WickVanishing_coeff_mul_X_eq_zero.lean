-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_mul_X_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:51.272851+00:00
-- url     : https://prove2.me/submissions/ceda7821-4ddf-4fd3-bd31-3b1d5110cdb3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {σ R : Type*} [CommRing R] (p : MvPowerSeries σ R) (s : σ) (n : σ →₀ ℕ) (hn : n s = 0) :
    coeff n (p * X s) = 0 := by
  rw [MvPowerSeries.X, MvPowerSeries.coeff_mul_monomial, if_neg]
  intro hle
  have h1 := Finsupp.le_def.1 hle s
  simp [hn] at h1
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
