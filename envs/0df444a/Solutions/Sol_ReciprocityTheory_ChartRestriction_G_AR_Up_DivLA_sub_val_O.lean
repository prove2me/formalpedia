-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.sub_val_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:10.497801+00:00
-- url     : https://prove2.me/submissions/2abd96e2-399e-4faa-a1bf-25a95a0329ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g 0 - g z) =O[𝓝 0] fun z => ‖z‖ ^ 1 := by
  have h := hg.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [sub_zero] at h
  have h2 := h.neg_left
  simp only [neg_sub] at h2
  simp only [pow_one]
  exact h2.trans (isBigO_norm_right.mpr (isBigO_refl _ _))
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
