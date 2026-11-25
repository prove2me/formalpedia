-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dof_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:57.024173+00:00
-- url     : https://prove2.me/submissions/be1a5f55-9a4b-4123-92bb-3e4882b5f095

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dofD_apply

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
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f + g) = Dof F v f + Dof F v g := by
  simp only [← dofD_apply, map_add]
end ReciprocityTheory.ChartRestriction.G.TB.GE
