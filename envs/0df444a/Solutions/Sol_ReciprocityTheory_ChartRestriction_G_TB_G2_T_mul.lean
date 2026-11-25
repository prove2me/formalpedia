-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.T_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:39:10.438206+00:00
-- url     : https://prove2.me/submissions/2fdef343-d37e-4803-8711-531299a12cf9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_list_sum
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
theorem _root_.solution (w : List ι) (A B : PS k 1 d) :
    T F u w (A * B) = ((splits w).map (fun p => T F u p.1 A * T F u p.2 B)).sum := by
  induction w with
  | nil => simp [splits, T]
  | cons l w ih =>
    rw [T_cons, ih, dof_list_sum, List.map_map]
    simp only [splits, List.map_append, List.map_map, List.sum_append]
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [dof_mul]
    rfl
end ReciprocityTheory.ChartRestriction.G.TB.G2
