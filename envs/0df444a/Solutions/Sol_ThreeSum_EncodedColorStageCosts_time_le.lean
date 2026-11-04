-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:57:25.803671+00:00
-- url     : https://prove2.me/submissions/ad560628-c395-41a4-bec4-15dc5cc5019a

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_source_time_mono
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_time_mono
import Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_time_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_mono
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_ModuloRuntime_time_mono
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.time n p M U xs ≤ time n P M U len := by
  have hw := (EncodedColorWantedCosts.time_le p M (microHalf (inputBits n))
    (blockCount (inputBits n)) U xs).trans (EncodedColorWantedCosts.time_mono hp hlen)
  have hs := source_time_mono (n := n) (U := U) (D := M) hp
  unfold LightEncodedColorWantedSources.time time
  omega
end ThreeSum.EncodedColorStageCosts
