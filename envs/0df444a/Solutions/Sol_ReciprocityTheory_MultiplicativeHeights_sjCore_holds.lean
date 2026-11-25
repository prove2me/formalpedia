-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sjCore_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:31:00.721227+00:00
-- url     : https://prove2.me/submissions/3db39d00-7b93-478c-91f1-c2de5dec5853

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCore
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gaussLogC_div
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_polar_mean
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radRatio_odd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : SphereLinLogStatement := by
  intro n c hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim c 0) hc
    · exact h
  obtain ⟨hi, he⟩ := polar_mean hn c hc
  refine ⟨hi, ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, gaussLogC_div hcn, h2, radRatio_odd]
  ring
end ReciprocityTheory.MultiplicativeHeights
