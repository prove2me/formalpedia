-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lu_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:45.725879+00:00
-- url     : https://prove2.me/submissions/a2514e6e-7891-41d5-83d2-ebfe05c06075

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lu_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_Mt_lu
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_one_add_sl_low
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_one_add_sl_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_up_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_up_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_eq_of_sl_up

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : Set.InjOn (lu (ι := ι) (r := r)) (sS ι r) := by
  intro w hw w' hw' h
  have key : ∀ τ, (1 + sl w τ) = (1 + sl w' τ) ∧ up w τ = up w' τ := by
    intro τ
    have hM : (1 + sl w τ) * up w τ = (1 + sl w' τ) * up w' τ := by
      rw [← Mt_lu, ← Mt_lu, h]
    exact lu_unique (one_add_sl_low w τ) (one_add_sl_diag w τ) (one_add_sl_low w' τ)
      (one_add_sl_diag w' τ) (up_upper w τ) (up_upper w' τ) (det_up_ne hw' τ) hM
  exact eq_of_sl_up (fun τ => add_left_cancel (key τ).1) (fun τ => (key τ).2)
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
