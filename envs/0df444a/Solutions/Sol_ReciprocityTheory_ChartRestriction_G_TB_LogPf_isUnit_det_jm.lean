-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.isUnit_det_jm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:25.433817+00:00
-- url     : https://prove2.me/submissions/ec09a6ac-90fd-49f6-acd5-0191687a6f8d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_jm_map_cc

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution : IsUnit (JM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have h : (constantCoeff : PS k 1 d →+* k).mapMatrix (JM G) = 1 := jm_map_cc G
  rw [h, Matrix.det_one]
  exact isUnit_one
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
