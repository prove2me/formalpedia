-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:41:27.308205+00:00
-- url     : https://prove2.me/submissions/8686332d-59b5-4dbd-9bbd-3761a187d50c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_jm_map_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_om_mul

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
theorem _root_.solution : (Om G).map constantCoeff = 1 := by
  have h := congrArg (fun M => M.map (constantCoeff : PS k 1 d →+* k)) (om_mul G)
  simp only [Matrix.map_mul] at h
  first
    | (rw [jm_map_cc, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h; exact h)
    | (simpa [jm_map_cc] using h)
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
