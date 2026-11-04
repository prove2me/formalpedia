-- Prove2me | solution 1 for ThreeSum.EncodedColorSourcesCosts.time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:16.026667+00:00
-- url     : https://prove2.me/submissions/bb8a6954-779f-4567-9f8e-079e81d2c043

import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorSourcesCosts
open Scales TrimScales BandScales
namespace ThreeSum.EncodedColorSourcesCosts
theorem _root_.solution (n p U M : ℕ) :
    time n p U M=SourceFiniteCosts.time n p U M+20*blockCount (inputBits n)+1020 := by
  unfold time LightNatPower.time
  omega
end ThreeSum.EncodedColorSourcesCosts
