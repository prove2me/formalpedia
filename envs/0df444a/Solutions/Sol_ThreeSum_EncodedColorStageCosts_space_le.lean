-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.space_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:47:16.964201+00:00
-- url     : https://prove2.me/submissions/58831520-3024-4cac-a018-a11a2118fff7

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_source_space_mono
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_base_le
import Theorems.Thm_ThreeSum_ColorBandBounds_space_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_space_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_space_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_space_mono
import Theorems.Thm_ThreeSum_SourceFiniteCosts_space_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {free n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.space free n p M U xs ≤ space free n P M U len := by
  have hw := (EncodedColorWantedCosts.space_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) U xs).trans (EncodedColorWantedCosts.space_mono hp hlen)
  exact max_le_max hw (source_space_mono (base_le hlen) hp)
end ThreeSum.EncodedColorStageCosts
