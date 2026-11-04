-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.base_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:16:48.740794+00:00
-- url     : https://prove2.me/submissions/8dda1009-6492-47ca-ad20-27b0489504cd

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_mono


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {free n p M len : ℕ} [NeZero M] {xs : List ℤ} (hlen : xs.length ≤ len) :
    LightEncodedColorFiniteSources.base free n p M xs ≤ sourceBase free n M len :=
  (EncodedColorWantedCosts.sourceBase_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs).trans (EncodedColorWantedCosts.sourceBase_mono hlen)
end ThreeSum.EncodedColorStageCosts
