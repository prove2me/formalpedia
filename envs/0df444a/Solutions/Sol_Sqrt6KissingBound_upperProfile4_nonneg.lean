-- Prove2me | solution 1 for Sqrt6KissingBound.upperProfile4_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:15:36.589065+00:00
-- url     : https://prove2.me/submissions/50477733-a02b-4b9e-9026-f6efdab51b89

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
private lemma s3_pos : 0 < s3_d4 := Real.sqrt_pos.2 (by norm_num)
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution {t : ℝ} (hta : a_d4 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ upperProfile4 t := by
  have hh : 0 ≤ 14 * t + 2 - 6 * s3_d4 := by
    dsimp [a_d4] at hta
    nlinarith [s3_pos]
  exact mul_nonneg (sub_nonneg.mpr ht1) hh
end Sqrt6KissingBound
