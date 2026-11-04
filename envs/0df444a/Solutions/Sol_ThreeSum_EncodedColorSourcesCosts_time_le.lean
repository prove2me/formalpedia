-- Prove2me | solution 1 for ThreeSum.EncodedColorSourcesCosts.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:15:42.700776+00:00
-- url     : https://prove2.me/submissions/5432d8b7-f9b9-44bf-907a-2131cbf59bbb

import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorSourcesCosts
open Scales TrimScales BandScales
namespace ThreeSum.EncodedColorSourcesCosts
theorem _root_.solution {NL NR n p U M : ℕ} (hn : 0 < n) (hL : NL ≤ n) (hR : NR ≤ n) :
    LightEncodedColorSources.time NL NR (bandSize n) p (microHalf (inputBits n))
      (blockCount (inputBits n)) (mu n) U M ≤ time n p U M := by
  have h := SourceFiniteCosts.time_le (p := p) (U := U) (D := M) hn hL hR
  unfold LightEncodedColorSources.time time
  omega
end ThreeSum.EncodedColorSourcesCosts
