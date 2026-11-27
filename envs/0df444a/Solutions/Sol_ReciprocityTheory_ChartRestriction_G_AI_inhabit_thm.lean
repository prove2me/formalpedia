-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.inhabit_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:46.723141+00:00
-- url     : https://prove2.me/submissions/6ce539e2-c11b-4cab-910e-0ac8dc9e9bfe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_Inhabit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : InhabitStatement := by
  refine ⟨Inhabit.model, ?_⟩
  change Inhabit.formI (fun _ => ![1, 0]) ≠ 0
  rw [Inhabit.formI_apply]
  simp
end ReciprocityTheory.ChartRestriction.G.AI
