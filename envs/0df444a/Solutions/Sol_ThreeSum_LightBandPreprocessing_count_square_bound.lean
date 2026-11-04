-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.count_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:17.723098+00:00
-- url     : https://prove2.me/submissions/3c554fe3-ebf3-421c-8f35-b0ae5e7cf2c5

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Theorems.Thm_ThreeSum_BandPartition_size_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
namespace ThreeSum.LightBandPreprocessing
theorem _root_.solution (a b c g : ℕ) :
    LightBandEnumeration.count (size a g) (size b g) (size c g) ≤
      3*(size (a+b+c) g)^2 := by
  have h := LightBandEnumeration.count_mono (size_mono (g := g) (show a ≤ a+b+c by omega))
    (size_mono (g := g) (show b ≤ a+b+c by omega)) (size_mono (g := g) (show c ≤ a+b+c by omega))
  convert h using 1 <;> unfold LightBandEnumeration.count <;> ring
end ThreeSum.LightBandPreprocessing
