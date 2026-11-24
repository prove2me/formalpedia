-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.ig_dlog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:39.474713+00:00
-- url     : https://prove2.me/submissions/13b9c264-fff6-4fc4-b0c9-db0607947b06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_map
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_map_pderiv__e784704e321e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_pderiv_expS

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
theorem _root_.solution [Algebra ℚ k] {n d : ℕ} (U : PS R n d) (hU : constantCoeff U = 1) (H : PS k n d)
    (hH : constantCoeff H = 0) (he : MvPowerSeries.map (algebraMap R k) U = FB.expS k H) (v : Fin n × Fin d) :
    pderiv k v H ∈ Ig R k (Fin n × Fin d) := by
  have h1 : pderiv k v (MvPowerSeries.map (algebraMap R k) U) =
      MvPowerSeries.map (algebraMap R k) U * pderiv k v H := by
    rw [he]
    exact pderiv_expS hH v
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 :=
    MvPowerSeries.mul_invOfUnit U 1 (by rw [hU, Units.val_one])
  have h2 : pderiv k v H =
      MvPowerSeries.map (algebraMap R k) (MvPowerSeries.invOfUnit U 1 * pderiv R v U) := by
    rw [map_mul, map_pderiv', h1, ← mul_assoc, ← map_mul, mul_comm (MvPowerSeries.invOfUnit U 1) U,
      hinv, map_one, one_mul]
  rw [h2]
  exact ig_map _
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
