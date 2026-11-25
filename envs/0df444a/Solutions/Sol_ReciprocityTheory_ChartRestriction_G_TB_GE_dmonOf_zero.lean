-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dmonOf_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:05:04.371666+00:00
-- url     : https://prove2.me/submissions/b248a352-1ba6-479a-89ad-b606e2e55139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dmonOf_Cmul

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (m : ι →₀ ℕ) : DmonOf F u m (0 : PS k 1 d) = 0 := by
  simpa using dmonOf_Cmul F u m (0 : k) (0 : PS k 1 d)
end ReciprocityTheory.ChartRestriction.G.TB.GE
