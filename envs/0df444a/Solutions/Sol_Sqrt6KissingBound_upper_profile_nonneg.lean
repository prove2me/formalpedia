-- Prove2me | solution 1 for Sqrt6KissingBound.upper_profile_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:27:03.769646+00:00
-- url     : https://prove2.me/submissions/19d630d6-3472-482c-9877-abf7137b306c

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {t : ℝ} (ht : t ≤ 1) :
    0 ≤ upperSlope_bg * (1 - t) := by
  positivity
end Sqrt6KissingBound
