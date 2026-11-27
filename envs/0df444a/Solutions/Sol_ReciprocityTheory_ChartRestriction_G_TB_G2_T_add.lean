-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.T_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:01.101001+00:00
-- url     : https://prove2.me/submissions/0249687f-1b00-49f8-ba45-2c985d2d2a84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_T_cons

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
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (w : List ι) (A B : PS k 1 d) : T F u w (A + B) = T F u w A + T F u w B := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [T_cons, T_cons, T_cons, ih, dof_add]
end ReciprocityTheory.ChartRestriction.G.TB.G2
