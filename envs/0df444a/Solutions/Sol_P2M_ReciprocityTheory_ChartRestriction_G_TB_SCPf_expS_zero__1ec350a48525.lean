-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_SCPf_expS_zero__1ec350a48525
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:04.18113+00:00
-- url     : https://prove2.me/submissions/6df0648f-fc10-49d9-a352-ca9c08a2e39a

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
theorem _root_.solution {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
