-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxGraph_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:28.92569+00:00
-- url     : https://prove2.me/submissions/d8189cbe-c59f-44d2-961f-fa8262ae207b

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraph
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_approxGraph_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_approxGraph_three
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_approxGraph_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ApproximationGraph
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : ApproxGraphStatement := by
  intro r p μ ρ X _ hμ hρ hρ1 hX
  exact ⟨fun w hw => approxGraph_one X hμ hρ hρ1 hX w hw,
    fun y hy hy0 => approxGraph_two X hμ hρ hρ1 hX y hy hy0,
    fun v y hy hvy => approxGraph_three X hμ hρ hρ1 hX v y hy hvy⟩
end ReciprocityTheory.MultiplicativeHeights
