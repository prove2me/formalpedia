-- Prove2me | solution 1 for ThreeSum.ColorBandBounds.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:03.861811+00:00
-- url     : https://prove2.me/submissions/dd125a0f-c473-4d27-a01b-a66ef11362e6

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_2186ec26acc49293
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace ThreeSum.ColorBandBounds
theorem _root_.solution {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.time a b c g ≤ time n g := by
  have ht := LightBandPreprocessing.time_bound a b c g
  have hc := count_le (g := g) hlen
  have hw := width_le (g := g) hlen
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 1000
    (show LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1 ≤
      count n g+n+1 by omega)) (Nat.add_le_add_right hw 1)
  unfold time
  rw [hlen] at ht
  omega
end ThreeSum.ColorBandBounds
