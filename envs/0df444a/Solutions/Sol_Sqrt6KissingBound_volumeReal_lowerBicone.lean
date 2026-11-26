-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_lowerBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:40.347025+00:00
-- url     : https://prove2.me/submissions/836c7b28-179c-4fe9-a973-0cde84ceb20e

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_lower_profile_integral
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_volumeReal_rotationalProfile_Ioo
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
private lemma s3_pos : 0 < s3_bv := Real.sqrt_pos.2 (by norm_num)
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (lowerBicone k) =
      (s3_bv / ((k + 2) * 2 ^ (k + 2))) * unitBallVolumeReal (k + 1) := by
  have h := volumeReal_rotationalProfile_Ioo k
    (a := (0 : ℝ)) (b := a_bv) (g := fun t => t / s3_bv)
    (by positivity) (continuous_id.div_const _)
    (by intro t ht; exact div_nonneg ht.1 s3_pos.le)
  simpa [lowerBicone, lower_profile_integral] using h
end Sqrt6KissingBound
