-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.Mt_lu_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:52.84365+00:00
-- url     : https://prove2.me/submissions/8c0c34bb-5e73-4ff8-bc45-fc2c8f3c09b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_one_add_sl_eS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_up_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (τ : ι) :
    Mt (lu ((eS ι r).symm (x, y))) τ = Nmat x τ * Umat y τ := by
  unfold Mt
  ext a b
  simp only [Matrix.of_apply, lu]
  rw [one_add_sl_eS, up_eS]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
