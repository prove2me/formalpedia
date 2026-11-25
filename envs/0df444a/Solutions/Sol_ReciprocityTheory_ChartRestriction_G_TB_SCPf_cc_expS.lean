-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:30.142827+00:00
-- url     : https://prove2.me/submissions/86412f3f-2ccc-44b1-aa14-d96085a8d8db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution {n : ℕ} (F : PS k n d) (hF : constantCoeff F = 0) : constantCoeff (FB.expS k F) = 1 := by
  have ha : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  have h2 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by simp
  unfold FB.expS
  rw [h1, ← PowerSeries.coe_substAlgHom ha, map_add, map_one, map_add, PowerSeries.coe_substAlgHom ha,
    PowerSeries.constantCoeff_subst_eq_zero hF _ h2, map_one, add_zero]
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
