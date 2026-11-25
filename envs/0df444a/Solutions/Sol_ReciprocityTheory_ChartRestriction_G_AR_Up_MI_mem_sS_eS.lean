-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.mem_sS_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:21.606854+00:00
-- url     : https://prove2.me/submissions/33d2c85f-de4c-48c8-9a3d-a907589ee3be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_eS_symm_apply

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
theorem _root_.solution (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) :
    (eS ι r).symm (x, y) ∈ sS ι r ↔ ∀ τ b, y (dI τ b) ≠ 0 := by
  simp [sS, eS_symm_apply, dI]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
