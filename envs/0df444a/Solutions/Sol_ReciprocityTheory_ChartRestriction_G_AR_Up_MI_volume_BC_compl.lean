-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.volume_BC_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:47.059911+00:00
-- url     : https://prove2.me/submissions/17c1f00e-bbdd-49a4-b884-3d2a917aa1ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_volume_lminor_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : volume (BC ι r)ᶜ = 0 := by
  have hU : (BC ι r)ᶜ = ⋃ τ : ι, ⋃ i : Fin (r + 1), {v : Ix ι r → ℂ | lminor (Mt v τ) i = 0} := by
    ext v
    simp [BC]
  rw [hU]
  refine measure_iUnion_null fun τ => measure_iUnion_null fun i => ?_
  exact volume_lminor_zero τ i.1 i.2
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
