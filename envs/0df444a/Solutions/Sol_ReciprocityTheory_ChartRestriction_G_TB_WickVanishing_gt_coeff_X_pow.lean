-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:22.861236+00:00
-- url     : https://prove2.me/submissions/33ae543c-1873-49c4-82f9-52bdc04f7879

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans

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
variable (A : Type) [CommRing A] [Algebra ℚ A]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (i : Fin 2) (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X i : MvPowerSeries (Fin 2) A) ^ n) = if e = single i n then 1 else 0 := by
  first
    | exact MvPowerSeries.coeff_X_pow e i n
    | (classical exact MvPowerSeries.coeff_X_pow e i n)
    | simp [MvPowerSeries.coeff_X_pow]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
