-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMaxPsh_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:49.433945+00:00
-- url     : https://prove2.me/submissions/84ab5694-4f68-4013-b5b4-240a72dc46e3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_usc
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_circle
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : RegMaxPshStatement := by
  intro D ι _ _ η U u hU hη hu
  refine ⟨regMax_usc η fun j => (hu j).1, fun z w hzw => ?_⟩
  have h := fun j => (hu j).2 z w hzw
  have hc := regMax_circle hη (fun ζ j => u j (z + ζ • w)) 0 1 fun j => (h j).1
  exact ⟨hc.1, le_trans (regMax_mono η fun j => (h j).2) hc.2⟩
end ReciprocityTheory.AnForm.A
