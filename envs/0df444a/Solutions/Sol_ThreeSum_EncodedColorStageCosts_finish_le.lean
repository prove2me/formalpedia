-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.finish_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:20:01.616952+00:00
-- url     : https://prove2.me/submissions/303edd11-6303-4855-8d21-27e7f0e0a4e1

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_SourceFiniteCosts_finish_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ SourceFiniteCosts.finish bound n := by
  apply (SourceFiniteCosts.finish_le hn hNL hNR).trans
  unfold SourceFiniteCosts.finish
  omega
end ThreeSum.EncodedColorStageCosts
