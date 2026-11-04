-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:30.766637+00:00
-- url     : https://prove2.me/submissions/6a008ab4-2070-4df4-a680-fe370fb9e48f

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
namespace ThreeSum.LightBandPreprocessing
theorem _root_.solution : program.length = 20 := by decide
end ThreeSum.LightBandPreprocessing
