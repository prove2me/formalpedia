-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.cells_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:34:26.476948+00:00
-- url     : https://prove2.me/submissions/72a95355-8518-4f2e-961f-3f23b56c60a0

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_local_envelope_le
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_space_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_bound
import Definitions.Def_WeightedCache3SUM_Alias_5ff3e9fe041ca03d
import Definitions.Def_WeightedCache3SUM_Alias_f0a4e431f2aa2c77
set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) : cells n ≤ envelope n :=
  by
  have hh := LocalParameterBounds.space_bound 0 (LightParameterInit.half n)
  have he := (local_envelope_le n).trans (scale_bounds n).2.2.2.1
  have hs := (scale_bounds n).1
  unfold cells LightParameterInit.space envelope
  omega
end ThreeSum.ThreeSumParameterResources
