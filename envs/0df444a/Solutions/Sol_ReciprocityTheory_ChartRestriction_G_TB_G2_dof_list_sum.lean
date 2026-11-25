-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.dof_list_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:43.419146+00:00
-- url     : https://prove2.me/submissions/fe2c4884-16e4-4215-b765-a315885e0e25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_zero

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) (v : Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (L : List (PS k 1 d)) : Dof F v L.sum = (L.map (Dof F v)).sum := by
  induction L with
  | nil => simp [dof_zero]
  | cons a L ih => simp [dof_add, ih]
end ReciprocityTheory.ChartRestriction.G.TB.G2
