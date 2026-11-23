-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_map_pderiv__e784704e321e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.330204+00:00
-- url     : https://prove2.me/submissions/4e5ac74f-8ac8-4796-bf0e-aeeb1940cd9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero

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
variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
variable {R k}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution {σ : Type} (f : MvPowerSeries σ R) (v : σ) :
    MvPowerSeries.map (algebraMap R k) (pderiv R v f) = pderiv k v (MvPowerSeries.map (algebraMap R k) f) := by
  ext n
  show coeff n (MvPowerSeries.map (algebraMap R k) (pderivFun v f)) =
    coeff n (pderivFun v (MvPowerSeries.map (algebraMap R k) f))
  unfold pderivFun
  show algebraMap R k (coeff (n + Finsupp.single v 1) f * ((n v : R) + 1)) =
    algebraMap R k (coeff (n + Finsupp.single v 1) f) * ((n v : k) + 1)
  rw [map_mul, map_add, map_one, map_natCast]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
