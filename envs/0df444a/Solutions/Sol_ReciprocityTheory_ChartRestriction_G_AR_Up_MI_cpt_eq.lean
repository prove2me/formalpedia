-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.cpt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:45.789264+00:00
-- url     : https://prove2.me/submissions/0da56397-ed12-4193-a622-3e89bef84971

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfL
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_NF__L_d63e5596805a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (x0 : Frame X.Ψ r) (z : V (nd X)) : cpt X x0 z = rmul x0 (NF X (ΦC X z)) := by
  show rmul x0 (nmat X z) = rmul x0 (NF X (ΦC X z))
  rw [← NF_ΦL]
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
