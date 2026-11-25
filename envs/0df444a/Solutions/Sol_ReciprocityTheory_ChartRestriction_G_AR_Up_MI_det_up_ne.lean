-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_up_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:56.469223+00:00
-- url     : https://prove2.me/submissions/d958cfba-90e7-4ee1-a040-7736e13b667a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_up

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
theorem _root_.solution {w : Ix ι r → ℂ} (hw : w ∈ sS ι r) (τ : ι) : (up w τ).det ≠ 0 := by
  rw [det_up]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => hw τ b
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
