-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:15.608204+00:00
-- url     : https://prove2.me/submissions/7000aed2-ac7a-402a-886b-8e68043b78bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (B : FB R d O) (a : O) (l : Fin d) : constantCoeff (B.actK k a l) = 0 := by
  show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.A.act a l)) = 0
  rw [MvPowerSeries.constantCoeff_map, B.A.const a l, map_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
