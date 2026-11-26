-- Prove2me | solution 1 for Sqrt6KissingBound.upperProfile3_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:14:33.341322+00:00
-- url     : https://prove2.me/submissions/51d14dbd-84d5-4b00-849d-5d2f959eb521

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    upperProfile3 t ^ 2 = 1 - t ^ 2 := by
  exact Real.sq_sqrt (by nlinarith)
end Sqrt6KissingBound
