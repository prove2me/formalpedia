-- Prove2me | solution 1 for ReciprocityTheory.AnForm.fsDens_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:24.857829+00:00
-- url     : https://prove2.me/submissions/f206dd5c-e660-47af-bbc2-67ca7525528d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution (z : ℂ) : 0 < fsDens z := by
  unfold fsDens; have := Real.pi_pos; positivity
end ReciprocityTheory.AnForm
