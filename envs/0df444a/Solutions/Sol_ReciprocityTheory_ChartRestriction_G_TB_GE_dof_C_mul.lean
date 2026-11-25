-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dof_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:03:02.50605+00:00
-- url     : https://prove2.me/submissions/1e2fd9a1-20df-4ed1-a06e-174ba68fd226

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C

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
theorem _root_.solution (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by
  rw [dof_mul, dof_C, mul_zero, add_zero]
end ReciprocityTheory.ChartRestriction.G.TB.GE
