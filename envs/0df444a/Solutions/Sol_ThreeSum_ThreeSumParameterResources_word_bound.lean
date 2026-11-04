-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:44:22.653475+00:00
-- url     : https://prove2.me/submissions/62d51f27-1bf8-4549-abf1-1ddc41787823

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_local_word_le
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_global_word_le
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) : LightParameterInit.word n ≤ envelope n := by
  have hn := (scale_bounds n).2.1
  have hb := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hy := (scale_bounds n).2.2.2.2.2
  have hl := local_word_le n
  have hg := global_word_le n
  unfold LightParameterInit.word envelope
  omega
end ThreeSum.ThreeSumParameterResources
